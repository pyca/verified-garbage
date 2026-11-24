// The functions of `src/ec_brainpoolp512r1_compressed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp512r1_compress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
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
	mov ebx, DWORD PTR [esp+8]
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
	mov ebx, DWORD PTR [esp+8]
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
	mov ecx, DWORD PTR [edi+2880]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+2368]
	and eax, 1
	or eax, 2
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+2176]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+61], eax
	mov eax, DWORD PTR [edi+2180]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+57], eax
	mov eax, DWORD PTR [edi+2184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+53], eax
	mov eax, DWORD PTR [edi+2188]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+49], eax
	mov eax, DWORD PTR [edi+2192]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+2196]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
	mov eax, DWORD PTR [edi+2200]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+2204]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+2208]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+2212]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+2216]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+2220]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+2224]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+2228]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+2232]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+2236]
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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-28]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+28]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_ec_brainpoolp512r1_decompress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
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
	mov ebx, DWORD PTR [esp+8]
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
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	mov DWORD PTR [edi+2112], edx
	or edx, 1
	xor edx, 3
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
	mov eax, DWORD PTR [edi+2752]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+2756]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+2760]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+2764]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+2768]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+2772]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+2776]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+2780]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+2784]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+2788]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+2792]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+2796]
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+2800]
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+2804]
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+2808]
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+2812]
	mov DWORD PTR [edi+1980], eax
	mov eax, DWORD PTR [edi+2752]
	mov DWORD PTR [edi+1984], eax
	mov eax, DWORD PTR [edi+2756]
	mov DWORD PTR [edi+1988], eax
	mov eax, DWORD PTR [edi+2760]
	mov DWORD PTR [edi+1992], eax
	mov eax, DWORD PTR [edi+2764]
	mov DWORD PTR [edi+1996], eax
	mov eax, DWORD PTR [edi+2768]
	mov DWORD PTR [edi+2000], eax
	mov eax, DWORD PTR [edi+2772]
	mov DWORD PTR [edi+2004], eax
	mov eax, DWORD PTR [edi+2776]
	mov DWORD PTR [edi+2008], eax
	mov eax, DWORD PTR [edi+2780]
	mov DWORD PTR [edi+2012], eax
	mov eax, DWORD PTR [edi+2784]
	mov DWORD PTR [edi+2016], eax
	mov eax, DWORD PTR [edi+2788]
	mov DWORD PTR [edi+2020], eax
	mov eax, DWORD PTR [edi+2792]
	mov DWORD PTR [edi+2024], eax
	mov eax, DWORD PTR [edi+2796]
	mov DWORD PTR [edi+2028], eax
	mov eax, DWORD PTR [edi+2800]
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [edi+2804]
	mov DWORD PTR [edi+2036], eax
	mov eax, DWORD PTR [edi+2808]
	mov DWORD PTR [edi+2040], eax
	mov eax, DWORD PTR [edi+2812]
	mov DWORD PTR [edi+2044], eax
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+892], eax
	mov esi, 1
20:
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
	test esi, esi
	jne 20b
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+2432], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+2436], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+2492], eax
	mov eax, 832
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
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+956], eax
	mov eax, 2432
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
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+1544], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+1548], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+1596], eax
	mov eax, 2432
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
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+1660], eax
	mov eax, 2432
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
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+1712], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+1716], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+1720], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+1724], eax
	mov eax, 2432
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
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+1728], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+1732], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+1736], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+1740], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+1744], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+1748], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+1752], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+1756], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+1760], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+1764], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+1768], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+1772], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+1776], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+1780], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+1784], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+1788], eax
	mov eax, 2432
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
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+1792], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+1796], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+1800], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+1804], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+1812], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+1832], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+1836], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+1840], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+1844], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+1848], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+1852], eax
	mov eax, 2432
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
	mov eax, DWORD PTR [edi+1920]
	mov DWORD PTR [edi+1856], eax
	mov eax, DWORD PTR [edi+1924]
	mov DWORD PTR [edi+1860], eax
	mov eax, DWORD PTR [edi+1928]
	mov DWORD PTR [edi+1864], eax
	mov eax, DWORD PTR [edi+1932]
	mov DWORD PTR [edi+1868], eax
	mov eax, DWORD PTR [edi+1936]
	mov DWORD PTR [edi+1872], eax
	mov eax, DWORD PTR [edi+1940]
	mov DWORD PTR [edi+1876], eax
	mov eax, DWORD PTR [edi+1944]
	mov DWORD PTR [edi+1880], eax
	mov eax, DWORD PTR [edi+1948]
	mov DWORD PTR [edi+1884], eax
	mov eax, DWORD PTR [edi+1952]
	mov DWORD PTR [edi+1888], eax
	mov eax, DWORD PTR [edi+1956]
	mov DWORD PTR [edi+1892], eax
	mov eax, DWORD PTR [edi+1960]
	mov DWORD PTR [edi+1896], eax
	mov eax, DWORD PTR [edi+1964]
	mov DWORD PTR [edi+1900], eax
	mov eax, DWORD PTR [edi+1968]
	mov DWORD PTR [edi+1904], eax
	mov eax, DWORD PTR [edi+1972]
	mov DWORD PTR [edi+1908], eax
	mov eax, DWORD PTR [edi+1976]
	mov DWORD PTR [edi+1912], eax
	mov eax, DWORD PTR [edi+1980]
	mov DWORD PTR [edi+1916], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+1980], eax
	mov esi, 4
21:
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
	test esi, esi
	jne 21b
	mov eax, 1536
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
	mov esi, 4
22:
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
	test esi, esi
	jne 22b
	mov eax, 1536
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
	mov esi, 4
23:
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
	test esi, esi
	jne 23b
	mov eax, 1728
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
	mov esi, 4
24:
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
	test esi, esi
	jne 24b
	mov eax, 1728
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
	mov esi, 4
25:
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
	test esi, esi
	jne 25b
	mov eax, 896
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
	mov esi, 4
26:
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
	test esi, esi
	jne 26b
	mov eax, 1728
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
	mov esi, 4
27:
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
	test esi, esi
	jne 27b
	mov eax, 1600
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
	mov esi, 4
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
	test esi, esi
	jne 28b
	mov eax, 832
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
	mov esi, 4
29:
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
	test esi, esi
	jne 29b
	mov eax, 1728
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
	mov esi, 4
210:
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
	test esi, esi
	jne 210b
	mov eax, 1600
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
	mov esi, 4
211:
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
	test esi, esi
	jne 211b
	mov eax, 1792
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
	mov esi, 5
212:
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
	test esi, esi
	jne 212b
	mov eax, 1600
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
	mov esi, 7
213:
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
	test esi, esi
	jne 213b
	mov eax, 1664
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
	mov esi, 7
214:
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
	test esi, esi
	jne 214b
	mov eax, 1728
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
	mov esi, 6
215:
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
	test esi, esi
	jne 215b
	mov eax, 1856
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
	mov esi, 4
216:
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
	test esi, esi
	jne 216b
	mov eax, 1856
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
	mov esi, 4
217:
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
	test esi, esi
	jne 217b
	mov eax, 1536
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
	mov esi, 5
218:
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
	test esi, esi
	jne 218b
	mov eax, 1600
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
	mov esi, 4
219:
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
	test esi, esi
	jne 219b
	mov eax, 896
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
	mov esi, 4
220:
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
	test esi, esi
	jne 220b
	mov eax, 1536
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
	mov esi, 4
221:
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
	test esi, esi
	jne 221b
	mov eax, 1600
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
	mov esi, 5
222:
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
	test esi, esi
	jne 222b
	mov eax, 896
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
	mov esi, 5
223:
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
	test esi, esi
	jne 223b
	mov eax, 1600
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
	mov esi, 4
224:
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
	test esi, esi
	jne 224b
	mov eax, 1664
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
	mov esi, 5
225:
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
	test esi, esi
	jne 225b
	mov eax, 1600
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
	mov esi, 4
226:
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
	test esi, esi
	jne 226b
	mov eax, 1856
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
	mov esi, 8
227:
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
	test esi, esi
	jne 227b
	mov eax, 832
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
	mov esi, 4
228:
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
	test esi, esi
	jne 228b
	mov eax, 1856
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
	mov esi, 6
229:
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
	test esi, esi
	jne 229b
	mov eax, 1728
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
	mov esi, 4
230:
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
	test esi, esi
	jne 230b
	mov eax, 896
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
	mov esi, 5
231:
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
	test esi, esi
	jne 231b
	mov eax, 832
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
	mov esi, 7
232:
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
	test esi, esi
	jne 232b
	mov eax, 1792
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
	mov esi, 4
233:
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
	test esi, esi
	jne 233b
	mov eax, 1728
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
	mov esi, 4
234:
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
	test esi, esi
	jne 234b
	mov eax, 896
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
	mov esi, 4
235:
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
	test esi, esi
	jne 235b
	mov eax, 1728
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
	mov esi, 5
236:
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
	test esi, esi
	jne 236b
	mov eax, 1600
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
	mov esi, 4
237:
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
	test esi, esi
	jne 237b
	mov eax, 1664
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
	mov esi, 5
238:
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
	test esi, esi
	jne 238b
	mov eax, 1600
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
	mov esi, 5
239:
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
	test esi, esi
	jne 239b
	mov eax, 1664
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
	mov esi, 7
240:
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
	test esi, esi
	jne 240b
	mov eax, 896
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
	mov esi, 4
241:
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
	test esi, esi
	jne 241b
	mov eax, 1728
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
	mov esi, 5
242:
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
	test esi, esi
	jne 242b
	mov eax, 1728
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
	mov esi, 4
243:
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
	test esi, esi
	jne 243b
	mov eax, 896
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
	mov esi, 6
244:
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
	test esi, esi
	jne 244b
	mov eax, 1600
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
	mov esi, 5
245:
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
	test esi, esi
	jne 245b
	mov eax, 1600
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
	mov esi, 4
246:
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
	test esi, esi
	jne 246b
	mov eax, 896
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
	mov esi, 5
247:
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
	test esi, esi
	jne 247b
	mov eax, 1536
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
	mov esi, 5
248:
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
	test esi, esi
	jne 248b
	mov eax, 1600
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
	mov esi, 8
249:
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
	test esi, esi
	jne 249b
	mov eax, 896
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
	mov esi, 4
250:
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
	test esi, esi
	jne 250b
	mov eax, 896
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
	mov esi, 5
251:
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
	test esi, esi
	jne 251b
	mov eax, 832
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
	mov esi, 7
252:
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
	test esi, esi
	jne 252b
	mov eax, 1600
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
	mov esi, 6
253:
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
	test esi, esi
	jne 253b
	mov eax, 1536
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
	mov esi, 4
254:
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
	test esi, esi
	jne 254b
	mov eax, 1856
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
	mov esi, 4
255:
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
	test esi, esi
	jne 255b
	mov eax, 1536
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
	mov esi, 6
256:
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
	test esi, esi
	jne 256b
	mov eax, 1792
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
	mov esi, 4
257:
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
	test esi, esi
	jne 257b
	mov eax, 1664
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
	mov esi, 4
258:
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
	test esi, esi
	jne 258b
	mov eax, 1728
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
	mov esi, 9
259:
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
	test esi, esi
	jne 259b
	mov eax, 832
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
	mov esi, 4
260:
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
	test esi, esi
	jne 260b
	mov eax, 896
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
	mov esi, 5
261:
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
	test esi, esi
	jne 261b
	mov eax, 1856
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
	mov esi, 5
262:
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
	test esi, esi
	jne 262b
	mov eax, 896
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
	mov esi, 6
263:
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
	test esi, esi
	jne 263b
	mov eax, 1792
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
	mov esi, 5
264:
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
	test esi, esi
	jne 264b
	mov eax, 832
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
	mov esi, 7
265:
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
	test esi, esi
	jne 265b
	mov eax, 1536
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
	mov esi, 5
266:
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
	test esi, esi
	jne 266b
	mov eax, 1728
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
	mov esi, 4
267:
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
	test esi, esi
	jne 267b
	mov eax, 1728
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
	mov esi, 4
268:
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
	test esi, esi
	jne 268b
	mov eax, 896
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
	mov esi, 5
269:
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
	test esi, esi
	jne 269b
	mov eax, 1792
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
	mov esi, 8
270:
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
	test esi, esi
	jne 270b
	mov eax, 1664
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
	mov esi, 4
271:
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
	test esi, esi
	jne 271b
	mov eax, 1536
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
	mov esi, 4
272:
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
	test esi, esi
	jne 272b
	mov eax, 1600
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
	mov esi, 4
273:
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
	test esi, esi
	jne 273b
	mov eax, 896
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
	mov esi, 4
274:
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
	test esi, esi
	jne 274b
	mov eax, 1536
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
	mov esi, 6
275:
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
	test esi, esi
	jne 275b
	mov eax, 1600
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
	mov esi, 10
276:
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
	test esi, esi
	jne 276b
	mov eax, 1600
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
	mov esi, 4
277:
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
	test esi, esi
	jne 277b
	mov eax, 896
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
	mov esi, 6
278:
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
	test esi, esi
	jne 278b
	mov eax, 1536
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
	mov esi, 4
279:
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
	test esi, esi
	jne 279b
	mov eax, 832
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
	mov esi, 10
280:
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
	test esi, esi
	jne 280b
	mov eax, 1856
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
	mov esi, 4
281:
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
	test esi, esi
	jne 281b
	mov eax, 1856
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
	mov esi, 4
282:
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
	test esi, esi
	jne 282b
	mov eax, 1664
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
	mov esi, 5
283:
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
	test esi, esi
	jne 283b
	mov eax, 1856
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
	mov esi, 5
284:
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
	test esi, esi
	jne 284b
	mov eax, 1536
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
	mov esi, 4
285:
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
	test esi, esi
	jne 285b
	mov eax, 1728
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
	mov esi, 9
286:
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
	test esi, esi
	jne 286b
	mov eax, 1728
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
	mov esi, 7
287:
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
	test esi, esi
	jne 287b
	mov eax, 1792
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
	mov esi, 7
288:
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
	test esi, esi
	jne 288b
	mov eax, 1536
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
	mov esi, 5
289:
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
	test esi, esi
	jne 289b
	mov eax, 1536
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
	mov esi, 6
290:
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
	test esi, esi
	jne 290b
	mov eax, 1536
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
	mov esi, 4
291:
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
	test esi, esi
	jne 291b
	mov eax, 1536
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
	mov esi, 4
292:
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
	test esi, esi
	jne 292b
	mov eax, 896
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
	mov esi, 7
293:
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
	test esi, esi
	jne 293b
	mov eax, 832
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
	mov esi, 5
294:
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
	test esi, esi
	jne 294b
	mov eax, 1728
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
	mov esi, 6
295:
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
	test esi, esi
	jne 295b
	mov eax, 1728
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
	mov esi, 6
296:
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
	test esi, esi
	jne 296b
	mov eax, 832
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
	mov esi, 4
297:
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
	test esi, esi
	jne 297b
	mov eax, 1792
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
	mov esi, 6
298:
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
	test esi, esi
	jne 298b
	mov eax, 1664
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
	mov esi, 5
299:
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
	test esi, esi
	jne 299b
	mov eax, 896
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
	mov esi, 4
2100:
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
	test esi, esi
	jne 2100b
	mov eax, 1792
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
	mov eax, 320
	mov ecx, 1920
	mov edx, 2368
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2368
	mov ecx, 256
	mov edx, 2432
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2368]
	mov ecx, DWORD PTR [edi+2112]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov eax, DWORD PTR [edi+2368]
	mov edx, DWORD PTR [edi+2432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [edi+2372]
	mov edx, DWORD PTR [edi+2436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [edi+2376]
	mov edx, DWORD PTR [edi+2440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [edi+2380]
	mov edx, DWORD PTR [edi+2444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [edi+2384]
	mov edx, DWORD PTR [edi+2448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [edi+2388]
	mov edx, DWORD PTR [edi+2452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [edi+2392]
	mov edx, DWORD PTR [edi+2456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [edi+2396]
	mov edx, DWORD PTR [edi+2460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [edi+2400]
	mov edx, DWORD PTR [edi+2464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [edi+2404]
	mov edx, DWORD PTR [edi+2468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [edi+2408]
	mov edx, DWORD PTR [edi+2472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [edi+2412]
	mov edx, DWORD PTR [edi+2476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [edi+2416]
	mov edx, DWORD PTR [edi+2480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [edi+2420]
	mov edx, DWORD PTR [edi+2484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [edi+2424]
	mov edx, DWORD PTR [edi+2488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [edi+2428]
	mov edx, DWORD PTR [edi+2492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2428], eax
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
	mov eax, 2752
	mov ecx, 2688
	mov edx, 2496
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+2496]
	or edx, DWORD PTR [edi+2500]
	or edx, DWORD PTR [edi+2504]
	or edx, DWORD PTR [edi+2508]
	or edx, DWORD PTR [edi+2512]
	or edx, DWORD PTR [edi+2516]
	or edx, DWORD PTR [edi+2520]
	or edx, DWORD PTR [edi+2524]
	or edx, DWORD PTR [edi+2528]
	or edx, DWORD PTR [edi+2532]
	or edx, DWORD PTR [edi+2536]
	or edx, DWORD PTR [edi+2540]
	or edx, DWORD PTR [edi+2544]
	or edx, DWORD PTR [edi+2548]
	or edx, DWORD PTR [edi+2552]
	or edx, DWORD PTR [edi+2556]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov eax, DWORD PTR [edi+2368]
	mov ecx, DWORD PTR [edi+2112]
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
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov ecx, DWORD PTR [edi+2880]
	mov ebx, DWORD PTR [esp+4]
	mov eax, 4
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+2176]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+61], eax
	mov eax, DWORD PTR [edi+2180]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+57], eax
	mov eax, DWORD PTR [edi+2184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+53], eax
	mov eax, DWORD PTR [edi+2188]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+49], eax
	mov eax, DWORD PTR [edi+2192]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+2196]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
	mov eax, DWORD PTR [edi+2200]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+2204]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+2208]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+2212]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+2216]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+2220]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+2224]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+2228]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+2232]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+2236]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, DWORD PTR [edi+2368]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+125], eax
	mov eax, DWORD PTR [edi+2372]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+121], eax
	mov eax, DWORD PTR [edi+2376]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+117], eax
	mov eax, DWORD PTR [edi+2380]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+113], eax
	mov eax, DWORD PTR [edi+2384]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+109], eax
	mov eax, DWORD PTR [edi+2388]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+105], eax
	mov eax, DWORD PTR [edi+2392]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+101], eax
	mov eax, DWORD PTR [edi+2396]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+97], eax
	mov eax, DWORD PTR [edi+2400]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+93], eax
	mov eax, DWORD PTR [edi+2404]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+89], eax
	mov eax, DWORD PTR [edi+2408]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+85], eax
	mov eax, DWORD PTR [edi+2412]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+81], eax
	mov eax, DWORD PTR [edi+2416]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+77], eax
	mov eax, DWORD PTR [edi+2420]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+73], eax
	mov eax, DWORD PTR [edi+2424]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+69], eax
	mov eax, DWORD PTR [edi+2428]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+65], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-28]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	lea esp, [esp+28]
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
