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

vg_ecdsa_brainpoolp512r1_sign:
	mov ecx, DWORD PTR [esp+24]
	mov ecx, DWORD PTR [ecx+12]
	cmp ecx, 0
	je 20f
	cmp ecx, 1
	je 22f
	cmp ecx, 2
	je 24f
	cmp ecx, 3
	je 26f
	cmp ecx, 4
	je 28f
	cmp ecx, 5
	je 210f
	cmp ecx, 6
	je 212f
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+228], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+232], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+236], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+256], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2413], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 161
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 289
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 1
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2413], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 161
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 289
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
214:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+356], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+364], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+368], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+376], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+380], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+384], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+392], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+396], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+400], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 215f
	mov edx, 0
	test edx, edx
	jmp 216f
215:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 33
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 161
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 160
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edx, 1
	test edx, edx
216:
	jne 214b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
	jmp 213f
212:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+232], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+236], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+256], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2409], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 157
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 285
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 1
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2409], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 157
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 285
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
217:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+356], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+364], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+368], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+376], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+380], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+384], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+392], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+396], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+400], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+416], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+420], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 218f
	mov edx, 0
	test edx, edx
	jmp 219f
218:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 29
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 157
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 156
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edx, 1
	test edx, edx
219:
	jne 217b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
213:
	jmp 211f
210:
	lea esp, [esp-260]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+272]
	mov eax, DWORD PTR [esi+60]
	bswap eax
	mov DWORD PTR [esp+256], eax
	sub eax, -1666645911
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esi+56]
	bswap eax
	mov DWORD PTR [esp+252], eax
	sbb eax, -1249405310
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esi+52]
	bswap eax
	mov DWORD PTR [esp+248], eax
	sbb eax, 140368605
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esi+48]
	bswap eax
	mov DWORD PTR [esp+244], eax
	sbb eax, 498193281
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esi+44]
	bswap eax
	mov DWORD PTR [esp+240], eax
	sbb eax, 2141982791
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esi+40]
	bswap eax
	mov DWORD PTR [esp+236], eax
	sbb eax, 1099325721
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esi+36]
	bswap eax
	mov DWORD PTR [esp+232], eax
	sbb eax, 1286153753
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esi+32]
	bswap eax
	mov DWORD PTR [esp+228], eax
	sbb eax, 1430150209
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esi+28]
	bswap eax
	mov DWORD PTR [esp+224], eax
	sbb eax, 1882392688
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+24]
	bswap eax
	mov DWORD PTR [esp+220], eax
	sbb eax, -698114870
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+216], eax
	sbb eax, -1278619122
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+212], eax
	sbb eax, -886010445
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+208], eax
	sbb eax, 868875271
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+204], eax
	sbb eax, 1070917294
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+200], eax
	sbb eax, -605436789
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+196], eax
	sbb eax, -1428316744
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+256]
	mov ecx, DWORD PTR [esp+60]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+256], eax
	mov eax, DWORD PTR [esp+252]
	mov ecx, DWORD PTR [esp+56]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esp+248]
	mov ecx, DWORD PTR [esp+52]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esp+244]
	mov ecx, DWORD PTR [esp+48]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esp+240]
	mov ecx, DWORD PTR [esp+44]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+40]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+236], eax
	mov eax, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+36]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+232], eax
	mov eax, DWORD PTR [esp+228]
	mov ecx, DWORD PTR [esp+32]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+228], eax
	mov eax, DWORD PTR [esp+224]
	mov ecx, DWORD PTR [esp+28]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+224], eax
	mov eax, DWORD PTR [esp+220]
	mov ecx, DWORD PTR [esp+24]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+220], eax
	mov eax, DWORD PTR [esp+216]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+216], eax
	mov eax, DWORD PTR [esp+212]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+212], eax
	mov eax, DWORD PTR [esp+208]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+208], eax
	mov eax, DWORD PTR [esp+204]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+204], eax
	mov eax, DWORD PTR [esp+200]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+200], eax
	mov eax, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+196], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+280]
	mov esi, DWORD PTR [esp+268]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 0
	mov BYTE PTR [edi+2320], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2413], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2417], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2421], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2425], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2429], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2433], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2437], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2441], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2445], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 2256
	mov ecx, 193
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov eax, 321
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov edi, DWORD PTR [esp+280]
	mov esi, DWORD PTR [esp+268]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 1
	mov BYTE PTR [edi+2320], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2413], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2417], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2421], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2425], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2429], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2433], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2437], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2441], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2445], eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 2256
	mov ecx, 193
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov eax, 321
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
220:
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov edi, DWORD PTR [esp+264]
	mov esi, DWORD PTR [esp+268]
	mov edx, DWORD PTR [esp+272]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+280]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 221f
	mov edx, 0
	test edx, edx
	jmp 222f
221:
	mov edi, DWORD PTR [esp+280]
	mov esi, DWORD PTR [esp+268]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 0
	mov BYTE PTR [edi+2320], al
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 2256
	mov ecx, 65
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov eax, 193
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esp+48]
	xor eax, ecx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esp+52]
	xor eax, ecx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esp+56]
	xor eax, ecx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esp+60]
	xor eax, ecx
	mov DWORD PTR [edi+1084], eax
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 0
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ecx, 64
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+280]
	add ebx, 256
	mov eax, 192
	mov ecx, 0
	mov edx, DWORD PTR [esp+280]
	add edx, 1152
	mov ebp, DWORD PTR [esp+280]
	add ebp, 512
	mov esi, DWORD PTR [esp+284]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+280]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov edx, 1
	test edx, edx
222:
	jne 220b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+260]
211:
	jmp 29f
28:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+212], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+216], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+220], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+224], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+228], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+232], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+236], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [esp+256], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, 0
	mov BYTE PTR [edi+2304], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2413], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2417], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2421], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2425], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2429], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 177
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 305
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, 1
	mov BYTE PTR [edi+2304], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2413], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2417], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2421], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2425], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2429], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 177
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 305
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
223:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+356], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+364], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+368], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+376], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+380], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+384], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+392], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+396], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+400], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+416], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+420], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+424], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+428], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+432], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 224f
	mov edx, 0
	test edx, edx
	jmp 225f
224:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, 0
	mov BYTE PTR [edi+2304], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 49
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 177
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+44], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esp+32]
	xor eax, ecx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esp+36]
	xor eax, ecx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esp+40]
	xor eax, ecx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esp+44]
	xor eax, ecx
	mov DWORD PTR [edi+1068], eax
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov DWORD PTR [edi+1088], ecx
	mov DWORD PTR [edi+1092], ecx
	mov DWORD PTR [edi+1096], ecx
	mov DWORD PTR [edi+1100], ecx
	mov DWORD PTR [edi+1104], ecx
	mov DWORD PTR [edi+1108], ecx
	mov DWORD PTR [edi+1112], ecx
	mov DWORD PTR [edi+1116], ecx
	mov DWORD PTR [edi+1120], ecx
	mov DWORD PTR [edi+1124], ecx
	mov DWORD PTR [edi+1128], ecx
	mov DWORD PTR [edi+1132], ecx
	mov DWORD PTR [edi+1136], ecx
	mov DWORD PTR [edi+1140], ecx
	mov DWORD PTR [edi+1144], ecx
	mov DWORD PTR [edi+1148], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 128
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 48
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 176
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esp+100], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esp+108], eax
	mov edx, 1
	test edx, edx
225:
	jne 223b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
29:
	jmp 27f
26:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+228], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+232], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+236], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+256], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2413], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 161
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 225
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 1
	mov BYTE PTR [edi+2288], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2413], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 161
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 225
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
226:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+356], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+364], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+368], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+376], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+380], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+384], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+392], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+396], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+400], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 227f
	mov edx, 0
	test edx, edx
	jmp 228f
227:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, 0
	mov BYTE PTR [edi+2288], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 33
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 97
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+28], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esp+28]
	xor eax, ecx
	mov DWORD PTR [edi+1052], eax
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 32
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 96
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esp+92], eax
	mov edx, 1
	test edx, edx
228:
	jne 226b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
27:
	jmp 25f
24:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+232], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+236], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+256], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2409], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 157
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 221
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 1
	mov BYTE PTR [edi+2284], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2409], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 157
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 221
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
229:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+356], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+364], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+368], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+376], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+380], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+384], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+392], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+396], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+400], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+416], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+420], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 230f
	mov edx, 0
	test edx, edx
	jmp 231f
230:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, 0
	mov BYTE PTR [edi+2284], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 29
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 93
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+24], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esp+20]
	xor eax, ecx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esp+24]
	xor eax, ecx
	mov DWORD PTR [edi+1048], eax
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 28
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 92
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esp+88], eax
	mov edx, 1
	test edx, edx
231:
	jne 229b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
25:
	jmp 23f
22:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+256], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, 0
	mov BYTE PTR [edi+2276], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2401], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 149
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 213
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, 1
	mov BYTE PTR [edi+2276], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2401], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 149
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 213
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
232:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+356], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+364], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+368], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+376], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+380], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+384], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+392], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+396], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+400], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+416], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 233f
	mov edx, 0
	test edx, edx
	jmp 234f
233:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, 0
	mov BYTE PTR [edi+2276], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 21
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 85
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+16], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esp+16]
	xor eax, ecx
	mov DWORD PTR [edi+1040], eax
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 20
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 84
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esp+80], eax
	mov edx, 1
	test edx, edx
234:
	jne 232b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
23:
	jmp 21f
20:
	lea esp, [esp-468]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+480]
	mov edi, DWORD PTR [esp+488]
	mov eax, 0
	mov DWORD PTR [esp+196], eax
	mov DWORD PTR [esp+200], eax
	mov DWORD PTR [esp+204], eax
	mov DWORD PTR [esp+208], eax
	mov DWORD PTR [esp+212], eax
	mov DWORD PTR [esp+216], eax
	mov DWORD PTR [esp+220], eax
	mov DWORD PTR [esp+224], eax
	mov DWORD PTR [esp+228], eax
	mov DWORD PTR [esp+232], eax
	mov DWORD PTR [esp+236], eax
	mov DWORD PTR [esp+240], eax
	mov DWORD PTR [esp+244], eax
	mov DWORD PTR [esp+248], eax
	mov DWORD PTR [esp+252], eax
	mov DWORD PTR [esp+256], eax
	mov DWORD PTR [esp+260], eax
	mov DWORD PTR [esp+264], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+256], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, 0
	mov BYTE PTR [edi+2272], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2273], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2397], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 145
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 209
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, 1
	mov BYTE PTR [edi+2272], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2273], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2277], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2281], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2285], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2289], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2293], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2297], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2301], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2305], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2309], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2313], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2317], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2397], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 145
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 209
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
235:
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+340], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+344], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+348], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+352], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+356], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+360], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+364], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+368], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+372], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+376], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+380], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+384], eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+3072]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi+3076]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+3080]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+3084]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+3088]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+3092]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+3096]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+3100]
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi+3104]
	mov DWORD PTR [edi+32], eax
	mov eax, DWORD PTR [edi+3108]
	mov DWORD PTR [edi+36], eax
	mov eax, DWORD PTR [edi+3112]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+3116]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+3120]
	mov DWORD PTR [edi+48], eax
	mov eax, DWORD PTR [edi+3124]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+3128]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+3132]
	mov DWORD PTR [edi+60], eax
	mov eax, DWORD PTR [edi+3136]
	mov DWORD PTR [edi+64], eax
	mov eax, DWORD PTR [edi+3140]
	mov DWORD PTR [edi+68], eax
	mov eax, DWORD PTR [edi+3144]
	mov DWORD PTR [edi+72], eax
	mov eax, DWORD PTR [edi+3148]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi+3152]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+3156]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+92], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+96], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+100], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+116], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+124], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+128], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+132], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+136], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+140], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+144], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+148], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+152], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+156], eax
	mov eax, DWORD PTR [edi+3232]
	mov DWORD PTR [edi+160], eax
	mov eax, DWORD PTR [edi+3236]
	mov DWORD PTR [edi+164], eax
	mov eax, DWORD PTR [edi+3240]
	mov DWORD PTR [edi+168], eax
	mov eax, DWORD PTR [edi+3244]
	mov DWORD PTR [edi+172], eax
	mov eax, DWORD PTR [edi+3248]
	mov DWORD PTR [edi+176], eax
	mov eax, DWORD PTR [edi+3252]
	mov DWORD PTR [edi+180], eax
	mov eax, DWORD PTR [edi+3256]
	mov DWORD PTR [edi+184], eax
	mov eax, DWORD PTR [edi+3260]
	mov DWORD PTR [edi+188], eax
	mov eax, DWORD PTR [edi+3264]
	mov DWORD PTR [edi+192], eax
	mov eax, DWORD PTR [edi+3268]
	mov DWORD PTR [edi+196], eax
	mov eax, DWORD PTR [edi+3272]
	mov DWORD PTR [edi+200], eax
	mov eax, DWORD PTR [edi+3276]
	mov DWORD PTR [edi+204], eax
	mov eax, DWORD PTR [edi+3280]
	mov DWORD PTR [edi+208], eax
	mov eax, DWORD PTR [edi+3284]
	mov DWORD PTR [edi+212], eax
	mov eax, DWORD PTR [edi+3288]
	mov DWORD PTR [edi+216], eax
	mov eax, DWORD PTR [edi+3292]
	mov DWORD PTR [edi+220], eax
	mov eax, DWORD PTR [edi+3296]
	mov DWORD PTR [edi+224], eax
	mov eax, DWORD PTR [edi+3300]
	mov DWORD PTR [edi+228], eax
	mov eax, DWORD PTR [edi+3304]
	mov DWORD PTR [edi+232], eax
	mov eax, DWORD PTR [edi+3308]
	mov DWORD PTR [edi+236], eax
	mov eax, DWORD PTR [edi+3312]
	mov DWORD PTR [edi+240], eax
	mov eax, DWORD PTR [edi+3316]
	mov DWORD PTR [edi+244], eax
	mov eax, DWORD PTR [edi+3320]
	mov DWORD PTR [edi+248], eax
	mov eax, DWORD PTR [edi+3324]
	mov DWORD PTR [edi+252], eax
	mov eax, DWORD PTR [edi+3328]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+3332]
	mov DWORD PTR [edi+260], eax
	mov eax, DWORD PTR [edi+3336]
	mov DWORD PTR [edi+264], eax
	mov eax, DWORD PTR [edi+3340]
	mov DWORD PTR [edi+268], eax
	mov eax, DWORD PTR [edi+3344]
	mov DWORD PTR [edi+272], eax
	mov eax, DWORD PTR [edi+3348]
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [edi+3352]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [edi+3356]
	mov DWORD PTR [edi+284], eax
	mov eax, DWORD PTR [edi+3360]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+3364]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+3368]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+3372]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+3376]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+3380]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+3384]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+3388]
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+3392]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [edi+3396]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [edi+3400]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [edi+3404]
	mov DWORD PTR [edi+332], eax
	mov eax, DWORD PTR [edi+3408]
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+3412]
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+3416]
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+3420]
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+3424]
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+3428]
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+3432]
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+3436]
	mov DWORD PTR [edi+364], eax
	mov eax, DWORD PTR [edi+3440]
	mov DWORD PTR [edi+368], eax
	mov eax, DWORD PTR [edi+3444]
	mov DWORD PTR [edi+372], eax
	mov eax, DWORD PTR [edi+3448]
	mov DWORD PTR [edi+376], eax
	mov eax, DWORD PTR [edi+3452]
	mov DWORD PTR [edi+380], eax
	mov eax, DWORD PTR [edi+3456]
	mov DWORD PTR [edi+384], eax
	mov eax, DWORD PTR [edi+3460]
	mov DWORD PTR [edi+388], eax
	mov eax, DWORD PTR [edi+3464]
	mov DWORD PTR [edi+392], eax
	mov eax, DWORD PTR [edi+3468]
	mov DWORD PTR [edi+396], eax
	mov eax, DWORD PTR [edi+3472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+3476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+3480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+3484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+3488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+3492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+3496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+3500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+3504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+3508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+3512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+3516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+3520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+3524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+3528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+3532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+3536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+3540]
	mov DWORD PTR [edi+468], eax
	mov eax, DWORD PTR [edi+3544]
	mov DWORD PTR [edi+472], eax
	mov eax, DWORD PTR [edi+3548]
	mov DWORD PTR [edi+476], eax
	mov eax, DWORD PTR [edi+3552]
	mov DWORD PTR [edi+480], eax
	mov eax, DWORD PTR [edi+3556]
	mov DWORD PTR [edi+484], eax
	mov eax, DWORD PTR [edi+3560]
	mov DWORD PTR [edi+488], eax
	mov eax, DWORD PTR [edi+3564]
	mov DWORD PTR [edi+492], eax
	mov eax, DWORD PTR [edi+3568]
	mov DWORD PTR [edi+496], eax
	mov eax, DWORD PTR [edi+3572]
	mov DWORD PTR [edi+500], eax
	mov eax, DWORD PTR [edi+3576]
	mov DWORD PTR [edi+504], eax
	mov eax, DWORD PTR [edi+3580]
	mov DWORD PTR [edi+508], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+392], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+396], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+400], eax
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 196
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign_k}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 236f
	mov edx, 0
	test edx, edx
	jmp 237f
236:
	mov edi, DWORD PTR [esp+488]
	mov esi, DWORD PTR [esp+476]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, 0
	mov BYTE PTR [edi+2272], al
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 2256
	mov ecx, 17
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 81
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+12], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi]
	push ebx
	call esi
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 909522486
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov ecx, 1549556828
	mov eax, DWORD PTR [esp]
	xor eax, ecx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esp+4]
	xor eax, ecx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esp+8]
	xor eax, ecx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esp+12]
	xor eax, ecx
	mov DWORD PTR [edi+1036], eax
	mov DWORD PTR [edi+1040], ecx
	mov DWORD PTR [edi+1044], ecx
	mov DWORD PTR [edi+1048], ecx
	mov DWORD PTR [edi+1052], ecx
	mov DWORD PTR [edi+1056], ecx
	mov DWORD PTR [edi+1060], ecx
	mov DWORD PTR [edi+1064], ecx
	mov DWORD PTR [edi+1068], ecx
	mov DWORD PTR [edi+1072], ecx
	mov DWORD PTR [edi+1076], ecx
	mov DWORD PTR [edi+1080], ecx
	mov DWORD PTR [edi+1084], ecx
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1024
	mov ecx, 64
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+128]
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+132]
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+136]
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+140]
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+144]
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+148]
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+152]
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+156]
	mov DWORD PTR [edi+3228], eax
	mov eax, DWORD PTR [edi+160]
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+164]
	mov DWORD PTR [edi+3236], eax
	mov eax, DWORD PTR [edi+168]
	mov DWORD PTR [edi+3240], eax
	mov eax, DWORD PTR [edi+172]
	mov DWORD PTR [edi+3244], eax
	mov eax, DWORD PTR [edi+176]
	mov DWORD PTR [edi+3248], eax
	mov eax, DWORD PTR [edi+180]
	mov DWORD PTR [edi+3252], eax
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+3256], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+3260], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+3264], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+3268], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+3272], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+3276], eax
	mov eax, DWORD PTR [edi+208]
	mov DWORD PTR [edi+3280], eax
	mov eax, DWORD PTR [edi+212]
	mov DWORD PTR [edi+3284], eax
	mov eax, DWORD PTR [edi+216]
	mov DWORD PTR [edi+3288], eax
	mov eax, DWORD PTR [edi+220]
	mov DWORD PTR [edi+3292], eax
	mov eax, DWORD PTR [edi+224]
	mov DWORD PTR [edi+3296], eax
	mov eax, DWORD PTR [edi+228]
	mov DWORD PTR [edi+3300], eax
	mov eax, DWORD PTR [edi+232]
	mov DWORD PTR [edi+3304], eax
	mov eax, DWORD PTR [edi+236]
	mov DWORD PTR [edi+3308], eax
	mov eax, DWORD PTR [edi+240]
	mov DWORD PTR [edi+3312], eax
	mov eax, DWORD PTR [edi+244]
	mov DWORD PTR [edi+3316], eax
	mov eax, DWORD PTR [edi+248]
	mov DWORD PTR [edi+3320], eax
	mov eax, DWORD PTR [edi+252]
	mov DWORD PTR [edi+3324], eax
	mov eax, DWORD PTR [edi+256]
	mov DWORD PTR [edi+3328], eax
	mov eax, DWORD PTR [edi+260]
	mov DWORD PTR [edi+3332], eax
	mov eax, DWORD PTR [edi+264]
	mov DWORD PTR [edi+3336], eax
	mov eax, DWORD PTR [edi+268]
	mov DWORD PTR [edi+3340], eax
	mov eax, DWORD PTR [edi+272]
	mov DWORD PTR [edi+3344], eax
	mov eax, DWORD PTR [edi+276]
	mov DWORD PTR [edi+3348], eax
	mov eax, DWORD PTR [edi+280]
	mov DWORD PTR [edi+3352], eax
	mov eax, DWORD PTR [edi+284]
	mov DWORD PTR [edi+3356], eax
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+3360], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+3364], eax
	mov eax, DWORD PTR [edi+296]
	mov DWORD PTR [edi+3368], eax
	mov eax, DWORD PTR [edi+300]
	mov DWORD PTR [edi+3372], eax
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+3376], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+3380], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+3384], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+3388], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+3392], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+3396], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+3400], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+3404], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+3408], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+3412], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+3416], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+3420], eax
	mov eax, DWORD PTR [edi+352]
	mov DWORD PTR [edi+3424], eax
	mov eax, DWORD PTR [edi+356]
	mov DWORD PTR [edi+3428], eax
	mov eax, DWORD PTR [edi+360]
	mov DWORD PTR [edi+3432], eax
	mov eax, DWORD PTR [edi+364]
	mov DWORD PTR [edi+3436], eax
	mov eax, DWORD PTR [edi+368]
	mov DWORD PTR [edi+3440], eax
	mov eax, DWORD PTR [edi+372]
	mov DWORD PTR [edi+3444], eax
	mov eax, DWORD PTR [edi+376]
	mov DWORD PTR [edi+3448], eax
	mov eax, DWORD PTR [edi+380]
	mov DWORD PTR [edi+3452], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+3456], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+3460], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+3464], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+3468], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+3472], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+3476], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+3480], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+3484], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+3488], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+3492], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+3496], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+3500], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+3504], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+3508], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+3512], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+3516], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+3520], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+3524], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+3528], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+3532], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+3536], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+3540], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+3544], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+3548], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+3552], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+3556], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+3560], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+3564], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+3568], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+3572], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+3576], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+3580], eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov edi, 64
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 0
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov edi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ecx, 16
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+4]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+488]
	add ebx, 256
	mov eax, 80
	mov ecx, 0
	mov edx, DWORD PTR [esp+488]
	add edx, 1152
	mov ebp, DWORD PTR [esp+488]
	add ebp, 512
	mov esi, DWORD PTR [esp+492]
	mov esi, DWORD PTR [esi+8]
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call esi
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+488]
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esp+76], eax
	mov edx, 1
	test edx, edx
237:
	jne 235b
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
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
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+468]
21:
	ret
	.p2align 6
