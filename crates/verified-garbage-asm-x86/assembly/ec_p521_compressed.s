// The functions of `src/ec_p521_compressed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_compress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2316], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2320], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2324], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2328], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2332], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2336], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2340], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2344], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2348], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2352], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2356], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2360], eax
	mov eax, 0
	mov DWORD PTR [edi+2364], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2428], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2432], eax
	mov eax, 0
	mov DWORD PTR [edi+2436], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2492], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2504], eax
	mov eax, 0
	mov DWORD PTR [edi+2508], eax
	mov eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, -1
	mov DWORD PTR [edi+68], eax
	mov eax, -1
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1
	mov DWORD PTR [edi+88], eax
	mov eax, -1
	mov DWORD PTR [edi+92], eax
	mov eax, -1
	mov DWORD PTR [edi+96], eax
	mov eax, -1
	mov DWORD PTR [edi+100], eax
	mov eax, -1
	mov DWORD PTR [edi+104], eax
	mov eax, -1
	mov DWORD PTR [edi+108], eax
	mov eax, -1
	mov DWORD PTR [edi+112], eax
	mov eax, -1
	mov DWORD PTR [edi+116], eax
	mov eax, -1
	mov DWORD PTR [edi+120], eax
	mov eax, -1
	mov DWORD PTR [edi+124], eax
	mov eax, 511
	mov DWORD PTR [edi+128], eax
	mov eax, 0
	mov DWORD PTR [edi+132], eax
	mov eax, -1858575351
	mov DWORD PTR [edi+136], eax
	mov eax, -1150306530
	mov DWORD PTR [edi+140], eax
	mov eax, -1986246738
	mov DWORD PTR [edi+144], eax
	mov eax, 1001769400
	mov DWORD PTR [edi+148], eax
	mov eax, -150362672
	mov DWORD PTR [edi+152], eax
	mov eax, 2144076104
	mov DWORD PTR [edi+156], eax
	mov eax, -1087400341
	mov DWORD PTR [edi+160], eax
	mov eax, 1367771011
	mov DWORD PTR [edi+164], eax
	mov eax, -6
	mov DWORD PTR [edi+168], eax
	mov eax, -1
	mov DWORD PTR [edi+172], eax
	mov eax, -1
	mov DWORD PTR [edi+176], eax
	mov eax, -1
	mov DWORD PTR [edi+180], eax
	mov eax, -1
	mov DWORD PTR [edi+184], eax
	mov eax, -1
	mov DWORD PTR [edi+188], eax
	mov eax, -1
	mov DWORD PTR [edi+192], eax
	mov eax, -1
	mov DWORD PTR [edi+196], eax
	mov eax, 511
	mov DWORD PTR [edi+200], eax
	mov eax, 0
	mov DWORD PTR [edi+204], eax
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
	mov eax, 0
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
	mov eax, 1
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
	mov eax, 0
	mov DWORD PTR [edi+384], eax
	mov eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, 0
	mov DWORD PTR [edi+412], eax
	mov eax, 0
	mov DWORD PTR [edi+416], eax
	mov eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, 8388608
	mov DWORD PTR [edi+428], eax
	mov eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, 0
	mov DWORD PTR [edi+448], eax
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, 0
	mov DWORD PTR [edi+472], eax
	mov eax, 0
	mov DWORD PTR [edi+476], eax
	mov eax, 0
	mov DWORD PTR [edi+480], eax
	mov eax, 0
	mov DWORD PTR [edi+484], eax
	mov eax, 0
	mov DWORD PTR [edi+488], eax
	mov eax, 0
	mov DWORD PTR [edi+492], eax
	mov eax, -1
	mov DWORD PTR [edi+496], eax
	mov eax, -25165825
	mov DWORD PTR [edi+500], eax
	mov eax, -1
	mov DWORD PTR [edi+504], eax
	mov eax, -1
	mov DWORD PTR [edi+508], eax
	mov eax, -1
	mov DWORD PTR [edi+512], eax
	mov eax, -1
	mov DWORD PTR [edi+516], eax
	mov eax, -1
	mov DWORD PTR [edi+520], eax
	mov eax, -1
	mov DWORD PTR [edi+524], eax
	mov eax, -1
	mov DWORD PTR [edi+528], eax
	mov eax, -1
	mov DWORD PTR [edi+532], eax
	mov eax, -1
	mov DWORD PTR [edi+536], eax
	mov eax, -1
	mov DWORD PTR [edi+540], eax
	mov eax, -1
	mov DWORD PTR [edi+544], eax
	mov eax, -1
	mov DWORD PTR [edi+548], eax
	mov eax, -1
	mov DWORD PTR [edi+552], eax
	mov eax, -1
	mov DWORD PTR [edi+556], eax
	mov eax, 511
	mov DWORD PTR [edi+560], eax
	mov eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, 185150101
	mov DWORD PTR [edi+568], eax
	mov eax, -2143473681
	mov DWORD PTR [edi+572], eax
	mov eax, -1096746914
	mov DWORD PTR [edi+576], eax
	mov eax, 1793517487
	mov DWORD PTR [edi+580], eax
	mov eax, 1281081935
	mov DWORD PTR [edi+584], eax
	mov eax, -1966068273
	mov DWORD PTR [edi+588], eax
	mov eax, 467241630
	mov DWORD PTR [edi+592], eax
	mov eax, 950107169
	mov DWORD PTR [edi+596], eax
	mov eax, -85803555
	mov DWORD PTR [edi+600], eax
	mov eax, -771676715
	mov DWORD PTR [edi+604], eax
	mov eax, 1515612558
	mov DWORD PTR [edi+608], eax
	mov eax, -308998450
	mov DWORD PTR [edi+612], eax
	mov eax, -1989768032
	mov DWORD PTR [edi+616], eax
	mov eax, 1710507947
	mov DWORD PTR [edi+620], eax
	mov eax, 1896990689
	mov DWORD PTR [edi+624], eax
	mov eax, 794552114
	mov DWORD PTR [edi+628], eax
	mov eax, 231
	mov DWORD PTR [edi+632], eax
	mov eax, 0
	mov DWORD PTR [edi+636], eax
	mov eax, -2119319295
	mov DWORD PTR [edi+640], eax
	mov eax, -1288593053
	mov DWORD PTR [edi+644], eax
	mov eax, 417428190
	mov DWORD PTR [edi+648], eax
	mov eax, 1308409663
	mov DWORD PTR [edi+652], eax
	mov eax, -524110559
	mov DWORD PTR [edi+656], eax
	mov eax, 1863951449
	mov DWORD PTR [edi+660], eax
	mov eax, -1814986796
	mov DWORD PTR [edi+664], eax
	mov eax, -1803612448
	mov DWORD PTR [edi+668], eax
	mov eax, 1006105516
	mov DWORD PTR [edi+672], eax
	mov eax, -581917265
	mov DWORD PTR [edi+676], eax
	mov eax, -1338661218
	mov DWORD PTR [edi+680], eax
	mov eax, -1862527913
	mov DWORD PTR [edi+684], eax
	mov eax, -1669160998
	mov DWORD PTR [edi+688], eax
	mov eax, 558772800
	mov DWORD PTR [edi+692], eax
	mov eax, -1290679590
	mov DWORD PTR [edi+696], eax
	mov eax, -422633627
	mov DWORD PTR [edi+700], eax
	mov eax, 116
	mov DWORD PTR [edi+704], eax
	mov eax, 0
	mov DWORD PTR [edi+708], eax
	mov eax, 1520313998
	mov DWORD PTR [edi+712], eax
	mov eax, 675679818
	mov DWORD PTR [edi+716], eax
	mov eax, 995092659
	mov DWORD PTR [edi+720], eax
	mov eax, 541351754
	mov DWORD PTR [edi+724], eax
	mov eax, 1129396577
	mov DWORD PTR [edi+728], eax
	mov eax, -1332044232
	mov DWORD PTR [edi+732], eax
	mov eax, -2137008509
	mov DWORD PTR [edi+736], eax
	mov eax, 543336540
	mov DWORD PTR [edi+740], eax
	mov eax, 1286568467
	mov DWORD PTR [edi+744], eax
	mov eax, 374077241
	mov DWORD PTR [edi+748], eax
	mov eax, -1953259725
	mov DWORD PTR [edi+752], eax
	mov eax, 873191390
	mov DWORD PTR [edi+756], eax
	mov eax, 615239074
	mov DWORD PTR [edi+760], eax
	mov eax, -322143582
	mov DWORD PTR [edi+764], eax
	mov eax, -636076403
	mov DWORD PTR [edi+768], eax
	mov eax, 36586799
	mov DWORD PTR [edi+772], eax
	mov eax, 480
	mov DWORD PTR [edi+776], eax
	mov eax, 0
	mov DWORD PTR [edi+780], eax
	mov eax, -820650748
	mov DWORD PTR [edi+784], eax
	mov eax, 326946893
	mov DWORD PTR [edi+788], eax
	mov eax, -447447389
	mov DWORD PTR [edi+792], eax
	mov eax, -150488356
	mov DWORD PTR [edi+796], eax
	mov eax, 2034594815
	mov DWORD PTR [edi+800], eax
	mov eax, 312970552
	mov DWORD PTR [edi+804], eax
	mov eax, 1475829254
	mov DWORD PTR [edi+808], eax
	mov eax, -747495691
	mov DWORD PTR [edi+812], eax
	mov eax, 776587227
	mov DWORD PTR [edi+816], eax
	mov eax, -579984424
	mov DWORD PTR [edi+820], eax
	mov eax, -1217040834
	mov DWORD PTR [edi+824], eax
	mov eax, -806104766
	mov DWORD PTR [edi+828], eax
	mov eax, -1461360708
	mov DWORD PTR [edi+832], eax
	mov eax, 1540124001
	mov DWORD PTR [edi+836], eax
	mov eax, 1227689285
	mov DWORD PTR [edi+840], eax
	mov eax, 764281809
	mov DWORD PTR [edi+844], eax
	mov eax, 61
	mov DWORD PTR [edi+848], eax
	mov eax, 0
	mov DWORD PTR [edi+852], eax
	mov eax, 0
	mov DWORD PTR [edi+856], eax
	mov eax, -75497472
	mov DWORD PTR [edi+860], eax
	mov eax, 1891066829
	mov DWORD PTR [edi+864], eax
	mov eax, 681723940
	mov DWORD PTR [edi+868], eax
	mov eax, 599470556
	mov DWORD PTR [edi+872], eax
	mov eax, 400696603
	mov DWORD PTR [edi+876], eax
	mov eax, 1535408941
	mov DWORD PTR [edi+880], eax
	mov eax, -901768705
	mov DWORD PTR [edi+884], eax
	mov eax, 1042311220
	mov DWORD PTR [edi+888], eax
	mov eax, 47660220
	mov DWORD PTR [edi+892], eax
	mov eax, 0
	mov DWORD PTR [edi+896], eax
	mov eax, 0
	mov DWORD PTR [edi+900], eax
	mov eax, 0
	mov DWORD PTR [edi+904], eax
	mov eax, 0
	mov DWORD PTR [edi+908], eax
	mov eax, 0
	mov DWORD PTR [edi+912], eax
	mov eax, 0
	mov DWORD PTR [edi+916], eax
	mov eax, 0
	mov DWORD PTR [edi+920], eax
	mov eax, 0
	mov DWORD PTR [edi+924], eax
	mov eax, -3
	mov DWORD PTR [edi+928], eax
	mov eax, -1
	mov DWORD PTR [edi+932], eax
	mov eax, -1
	mov DWORD PTR [edi+936], eax
	mov eax, -1
	mov DWORD PTR [edi+940], eax
	mov eax, -1
	mov DWORD PTR [edi+944], eax
	mov eax, -1
	mov DWORD PTR [edi+948], eax
	mov eax, -1
	mov DWORD PTR [edi+952], eax
	mov eax, -1
	mov DWORD PTR [edi+956], eax
	mov eax, -1
	mov DWORD PTR [edi+960], eax
	mov eax, -1
	mov DWORD PTR [edi+964], eax
	mov eax, -1
	mov DWORD PTR [edi+968], eax
	mov eax, -1
	mov DWORD PTR [edi+972], eax
	mov eax, -1
	mov DWORD PTR [edi+976], eax
	mov eax, -1
	mov DWORD PTR [edi+980], eax
	mov eax, -1
	mov DWORD PTR [edi+984], eax
	mov eax, -1
	mov DWORD PTR [edi+988], eax
	mov eax, 511
	mov DWORD PTR [edi+992], eax
	mov eax, 0
	mov DWORD PTR [edi+996], eax
	mov eax, -1858575353
	mov DWORD PTR [edi+1000], eax
	mov eax, -1150306530
	mov DWORD PTR [edi+1004], eax
	mov eax, -1986246738
	mov DWORD PTR [edi+1008], eax
	mov eax, 1001769400
	mov DWORD PTR [edi+1012], eax
	mov eax, -150362672
	mov DWORD PTR [edi+1016], eax
	mov eax, 2144076104
	mov DWORD PTR [edi+1020], eax
	mov eax, -1087400341
	mov DWORD PTR [edi+1024], eax
	mov eax, 1367771011
	mov DWORD PTR [edi+1028], eax
	mov eax, -6
	mov DWORD PTR [edi+1032], eax
	mov eax, -1
	mov DWORD PTR [edi+1036], eax
	mov eax, -1
	mov DWORD PTR [edi+1040], eax
	mov eax, -1
	mov DWORD PTR [edi+1044], eax
	mov eax, -1
	mov DWORD PTR [edi+1048], eax
	mov eax, -1
	mov DWORD PTR [edi+1052], eax
	mov eax, -1
	mov DWORD PTR [edi+1056], eax
	mov eax, -1
	mov DWORD PTR [edi+1060], eax
	mov eax, 511
	mov DWORD PTR [edi+1064], eax
	mov eax, 0
	mov DWORD PTR [edi+1068], eax
	mov eax, 0
	mov DWORD PTR [edi+1072], eax
	mov eax, 0
	mov DWORD PTR [edi+1076], eax
	mov eax, 0
	mov DWORD PTR [edi+1080], eax
	mov eax, 0
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
	mov eax, 8388608
	mov DWORD PTR [edi+1148], eax
	mov eax, 0
	mov DWORD PTR [edi+1152], eax
	mov eax, 0
	mov DWORD PTR [edi+1156], eax
	mov eax, 0
	mov DWORD PTR [edi+1160], eax
	mov eax, 0
	mov DWORD PTR [edi+1164], eax
	mov eax, 0
	mov DWORD PTR [edi+1168], eax
	mov eax, 0
	mov DWORD PTR [edi+1172], eax
	mov eax, 0
	mov DWORD PTR [edi+1176], eax
	mov eax, 0
	mov DWORD PTR [edi+1180], eax
	mov eax, 0
	mov DWORD PTR [edi+1184], eax
	mov eax, 0
	mov DWORD PTR [edi+1188], eax
	mov eax, 0
	mov DWORD PTR [edi+1192], eax
	mov eax, 0
	mov DWORD PTR [edi+1196], eax
	mov eax, 0
	mov DWORD PTR [edi+1200], eax
	mov eax, 0
	mov DWORD PTR [edi+1204], eax
	mov eax, 0
	mov DWORD PTR [edi+1208], eax
	mov eax, 0
	mov DWORD PTR [edi+1212], eax
	mov eax, 0
	mov DWORD PTR [edi+1216], eax
	mov eax, 0
	mov DWORD PTR [edi+1220], eax
	mov eax, 0
	mov DWORD PTR [edi+1224], eax
	mov eax, 0
	mov DWORD PTR [edi+1228], eax
	mov eax, 0
	mov DWORD PTR [edi+1232], eax
	mov eax, 0
	mov DWORD PTR [edi+1236], eax
	mov eax, 0
	mov DWORD PTR [edi+1240], eax
	mov eax, 0
	mov DWORD PTR [edi+1244], eax
	mov eax, 0
	mov DWORD PTR [edi+1248], eax
	mov eax, 0
	mov DWORD PTR [edi+1252], eax
	mov eax, 0
	mov DWORD PTR [edi+1256], eax
	mov eax, 0
	mov DWORD PTR [edi+1260], eax
	mov eax, 0
	mov DWORD PTR [edi+1264], eax
	mov eax, 0
	mov DWORD PTR [edi+1268], eax
	mov eax, 0
	mov DWORD PTR [edi+1272], eax
	mov eax, 0
	mov DWORD PTR [edi+1276], eax
	mov eax, 0
	mov DWORD PTR [edi+1280], eax
	mov eax, 0
	mov DWORD PTR [edi+1284], eax
	mov eax, -1
	mov DWORD PTR [edi+3232], eax
	mov eax, 0
	mov DWORD PTR [edi+2872], eax
	mov eax, 0
	mov DWORD PTR [edi+2876], eax
	mov eax, 0
	mov DWORD PTR [edi+2880], eax
	mov eax, 16384
	mov DWORD PTR [edi+2884], eax
	mov eax, 0
	mov DWORD PTR [edi+2888], eax
	mov eax, 0
	mov DWORD PTR [edi+2892], eax
	mov eax, 0
	mov DWORD PTR [edi+2896], eax
	mov eax, 0
	mov DWORD PTR [edi+2900], eax
	mov eax, 0
	mov DWORD PTR [edi+2904], eax
	mov eax, 0
	mov DWORD PTR [edi+2908], eax
	mov eax, 0
	mov DWORD PTR [edi+2912], eax
	mov eax, 0
	mov DWORD PTR [edi+2916], eax
	mov eax, 0
	mov DWORD PTR [edi+2920], eax
	mov eax, 0
	mov DWORD PTR [edi+2924], eax
	mov eax, 0
	mov DWORD PTR [edi+2928], eax
	mov eax, 0
	mov DWORD PTR [edi+2932], eax
	mov eax, 0
	mov DWORD PTR [edi+2936], eax
	mov eax, 0
	mov DWORD PTR [edi+2940], eax
	mov eax, -1369939065
	mov DWORD PTR [edi+2944], eax
	mov eax, -2146146993
	mov DWORD PTR [edi+2948], eax
	mov eax, -365582305
	mov DWORD PTR [edi+2952], eax
	mov eax, 2029494927
	mov DWORD PTR [edi+2956], eax
	mov eax, -1004628454
	mov DWORD PTR [edi+2960], eax
	mov eax, -2087011857
	mov DWORD PTR [edi+2964], eax
	mov eax, 1587402975
	mov DWORD PTR [edi+2968], eax
	mov eax, -1114953376
	mov DWORD PTR [edi+2972], eax
	mov eax, -1460256951
	mov DWORD PTR [edi+2976], eax
	mov eax, -257225572
	mov DWORD PTR [edi+2980], eax
	mov eax, -926451580
	mov DWORD PTR [edi+2984], eax
	mov eax, -102999484
	mov DWORD PTR [edi+2988], eax
	mov eax, 768399754
	mov DWORD PTR [edi+2992], eax
	mov eax, 2001825081
	mov DWORD PTR [edi+2996], eax
	mov eax, -799325536
	mov DWORD PTR [edi+3000], eax
	mov eax, 264850704
	mov DWORD PTR [edi+3004], eax
	mov eax, 77
	mov DWORD PTR [edi+3008], eax
	mov eax, 0
	mov DWORD PTR [edi+3012], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2492], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2504], eax
	mov eax, 0
	mov DWORD PTR [edi+2508], eax
	add ebx, 66
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2656], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2660], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2664], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2668], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2672], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2676], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2680], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2684], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2688], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2692], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2696], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2700], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2708], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2720], eax
	mov eax, 0
	mov DWORD PTR [edi+2724], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov edx, DWORD PTR [edi+2440]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+2444]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+2448]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+2452]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+2456]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+2460]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+2464]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+2468]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+2472]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+2476]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+2480]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+2484]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+2488]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+2492]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+2496]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+2500]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+2504]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+2508]
	sbb edx, DWORD PTR [edi+132]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov edx, DWORD PTR [edi+2656]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+2660]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+2664]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+2668]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+2672]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+2676]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+2680]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+2684]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+2688]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+2692]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+2696]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+2700]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+2704]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+2708]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+2712]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+2716]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+2720]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+2724]
	sbb edx, DWORD PTR [edi+132]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov eax, 2872
	mov ecx, 2440
	mov edx, 2512
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2872
	mov ecx, 2656
	mov edx, 2584
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2584
	mov ecx, 2584
	mov edx, 2728
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2512
	mov ecx, 2512
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2512
	mov ecx, 3016
	mov edx, 3088
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2512
	mov ecx, 496
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3016
	mov ecx, 3088
	mov edx, 2800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2944
	mov ecx, 2800
	mov edx, 3088
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3088
	mov ecx, 2728
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+3016]
	or edx, DWORD PTR [edi+3020]
	or edx, DWORD PTR [edi+3024]
	or edx, DWORD PTR [edi+3028]
	or edx, DWORD PTR [edi+3032]
	or edx, DWORD PTR [edi+3036]
	or edx, DWORD PTR [edi+3040]
	or edx, DWORD PTR [edi+3044]
	or edx, DWORD PTR [edi+3048]
	or edx, DWORD PTR [edi+3052]
	or edx, DWORD PTR [edi+3056]
	or edx, DWORD PTR [edi+3060]
	or edx, DWORD PTR [edi+3064]
	or edx, DWORD PTR [edi+3068]
	or edx, DWORD PTR [edi+3072]
	or edx, DWORD PTR [edi+3076]
	or edx, DWORD PTR [edi+3080]
	or edx, DWORD PTR [edi+3084]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov ecx, DWORD PTR [edi+3232]
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+2512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+2516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2804], eax
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+2520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2808], eax
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+2524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2812], eax
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+2528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2816], eax
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+2532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2820], eax
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+2536]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2824], eax
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+2540]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2828], eax
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+2544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2832], eax
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+2548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2836], eax
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+2552]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2840], eax
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+2556]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2844], eax
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+2560]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2848], eax
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+2564]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2852], eax
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+2568]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2856], eax
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+2572]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2860], eax
	mov eax, DWORD PTR [edi+704]
	mov edx, DWORD PTR [edi+2576]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2864], eax
	mov eax, DWORD PTR [edi+708]
	mov edx, DWORD PTR [edi+2580]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2868], eax
	mov eax, DWORD PTR [edi+712]
	mov edx, DWORD PTR [edi+2584]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3160], eax
	mov eax, DWORD PTR [edi+716]
	mov edx, DWORD PTR [edi+2588]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3164], eax
	mov eax, DWORD PTR [edi+720]
	mov edx, DWORD PTR [edi+2592]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3168], eax
	mov eax, DWORD PTR [edi+724]
	mov edx, DWORD PTR [edi+2596]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3172], eax
	mov eax, DWORD PTR [edi+728]
	mov edx, DWORD PTR [edi+2600]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3176], eax
	mov eax, DWORD PTR [edi+732]
	mov edx, DWORD PTR [edi+2604]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3180], eax
	mov eax, DWORD PTR [edi+736]
	mov edx, DWORD PTR [edi+2608]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3184], eax
	mov eax, DWORD PTR [edi+740]
	mov edx, DWORD PTR [edi+2612]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3188], eax
	mov eax, DWORD PTR [edi+744]
	mov edx, DWORD PTR [edi+2616]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3192], eax
	mov eax, DWORD PTR [edi+748]
	mov edx, DWORD PTR [edi+2620]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3196], eax
	mov eax, DWORD PTR [edi+752]
	mov edx, DWORD PTR [edi+2624]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3200], eax
	mov eax, DWORD PTR [edi+756]
	mov edx, DWORD PTR [edi+2628]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3204], eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+2632]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3208], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+2636]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3212], eax
	mov eax, DWORD PTR [edi+768]
	mov edx, DWORD PTR [edi+2640]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3216], eax
	mov eax, DWORD PTR [edi+772]
	mov edx, DWORD PTR [edi+2644]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3220], eax
	mov eax, DWORD PTR [edi+776]
	mov edx, DWORD PTR [edi+2648]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3224], eax
	mov eax, DWORD PTR [edi+780]
	mov edx, DWORD PTR [edi+2652]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+3228], eax
	mov ecx, DWORD PTR [edi+3232]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+2656]
	and eax, 1
	or eax, 2
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+2440]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+63], eax
	mov eax, DWORD PTR [edi+2444]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+59], eax
	mov eax, DWORD PTR [edi+2448]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+55], eax
	mov eax, DWORD PTR [edi+2452]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+51], eax
	mov eax, DWORD PTR [edi+2456]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+47], eax
	mov eax, DWORD PTR [edi+2460]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+43], eax
	mov eax, DWORD PTR [edi+2464]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+39], eax
	mov eax, DWORD PTR [edi+2468]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+35], eax
	mov eax, DWORD PTR [edi+2472]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+31], eax
	mov eax, DWORD PTR [edi+2476]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+27], eax
	mov eax, DWORD PTR [edi+2480]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+23], eax
	mov eax, DWORD PTR [edi+2484]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+19], eax
	mov eax, DWORD PTR [edi+2488]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+15], eax
	mov eax, DWORD PTR [edi+2492]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+11], eax
	mov eax, DWORD PTR [edi+2496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+7], eax
	mov eax, DWORD PTR [edi+2500]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+3], eax
	mov eax, DWORD PTR [edi+2504]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [ebx+1], dl
	mov edx, eax
	mov BYTE PTR [ebx+2], dl
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6

vg_ec_p521_decompress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2316], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2320], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2324], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2328], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2332], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2336], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2340], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2344], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2348], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2352], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2356], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2360], eax
	mov eax, 0
	mov DWORD PTR [edi+2364], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2428], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2432], eax
	mov eax, 0
	mov DWORD PTR [edi+2436], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2492], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2504], eax
	mov eax, 0
	mov DWORD PTR [edi+2508], eax
	mov eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, -1
	mov DWORD PTR [edi+68], eax
	mov eax, -1
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1
	mov DWORD PTR [edi+88], eax
	mov eax, -1
	mov DWORD PTR [edi+92], eax
	mov eax, -1
	mov DWORD PTR [edi+96], eax
	mov eax, -1
	mov DWORD PTR [edi+100], eax
	mov eax, -1
	mov DWORD PTR [edi+104], eax
	mov eax, -1
	mov DWORD PTR [edi+108], eax
	mov eax, -1
	mov DWORD PTR [edi+112], eax
	mov eax, -1
	mov DWORD PTR [edi+116], eax
	mov eax, -1
	mov DWORD PTR [edi+120], eax
	mov eax, -1
	mov DWORD PTR [edi+124], eax
	mov eax, 511
	mov DWORD PTR [edi+128], eax
	mov eax, 0
	mov DWORD PTR [edi+132], eax
	mov eax, -1858575351
	mov DWORD PTR [edi+136], eax
	mov eax, -1150306530
	mov DWORD PTR [edi+140], eax
	mov eax, -1986246738
	mov DWORD PTR [edi+144], eax
	mov eax, 1001769400
	mov DWORD PTR [edi+148], eax
	mov eax, -150362672
	mov DWORD PTR [edi+152], eax
	mov eax, 2144076104
	mov DWORD PTR [edi+156], eax
	mov eax, -1087400341
	mov DWORD PTR [edi+160], eax
	mov eax, 1367771011
	mov DWORD PTR [edi+164], eax
	mov eax, -6
	mov DWORD PTR [edi+168], eax
	mov eax, -1
	mov DWORD PTR [edi+172], eax
	mov eax, -1
	mov DWORD PTR [edi+176], eax
	mov eax, -1
	mov DWORD PTR [edi+180], eax
	mov eax, -1
	mov DWORD PTR [edi+184], eax
	mov eax, -1
	mov DWORD PTR [edi+188], eax
	mov eax, -1
	mov DWORD PTR [edi+192], eax
	mov eax, -1
	mov DWORD PTR [edi+196], eax
	mov eax, 511
	mov DWORD PTR [edi+200], eax
	mov eax, 0
	mov DWORD PTR [edi+204], eax
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
	mov eax, 0
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
	mov eax, 1
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
	mov eax, 0
	mov DWORD PTR [edi+384], eax
	mov eax, 0
	mov DWORD PTR [edi+388], eax
	mov eax, 0
	mov DWORD PTR [edi+392], eax
	mov eax, 0
	mov DWORD PTR [edi+396], eax
	mov eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, 0
	mov DWORD PTR [edi+412], eax
	mov eax, 0
	mov DWORD PTR [edi+416], eax
	mov eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, 0
	mov DWORD PTR [edi+424], eax
	mov eax, 8388608
	mov DWORD PTR [edi+428], eax
	mov eax, 0
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, 0
	mov DWORD PTR [edi+448], eax
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, 0
	mov DWORD PTR [edi+472], eax
	mov eax, 0
	mov DWORD PTR [edi+476], eax
	mov eax, 0
	mov DWORD PTR [edi+480], eax
	mov eax, 0
	mov DWORD PTR [edi+484], eax
	mov eax, 0
	mov DWORD PTR [edi+488], eax
	mov eax, 0
	mov DWORD PTR [edi+492], eax
	mov eax, -1
	mov DWORD PTR [edi+496], eax
	mov eax, -25165825
	mov DWORD PTR [edi+500], eax
	mov eax, -1
	mov DWORD PTR [edi+504], eax
	mov eax, -1
	mov DWORD PTR [edi+508], eax
	mov eax, -1
	mov DWORD PTR [edi+512], eax
	mov eax, -1
	mov DWORD PTR [edi+516], eax
	mov eax, -1
	mov DWORD PTR [edi+520], eax
	mov eax, -1
	mov DWORD PTR [edi+524], eax
	mov eax, -1
	mov DWORD PTR [edi+528], eax
	mov eax, -1
	mov DWORD PTR [edi+532], eax
	mov eax, -1
	mov DWORD PTR [edi+536], eax
	mov eax, -1
	mov DWORD PTR [edi+540], eax
	mov eax, -1
	mov DWORD PTR [edi+544], eax
	mov eax, -1
	mov DWORD PTR [edi+548], eax
	mov eax, -1
	mov DWORD PTR [edi+552], eax
	mov eax, -1
	mov DWORD PTR [edi+556], eax
	mov eax, 511
	mov DWORD PTR [edi+560], eax
	mov eax, 0
	mov DWORD PTR [edi+564], eax
	mov eax, 185150101
	mov DWORD PTR [edi+568], eax
	mov eax, -2143473681
	mov DWORD PTR [edi+572], eax
	mov eax, -1096746914
	mov DWORD PTR [edi+576], eax
	mov eax, 1793517487
	mov DWORD PTR [edi+580], eax
	mov eax, 1281081935
	mov DWORD PTR [edi+584], eax
	mov eax, -1966068273
	mov DWORD PTR [edi+588], eax
	mov eax, 467241630
	mov DWORD PTR [edi+592], eax
	mov eax, 950107169
	mov DWORD PTR [edi+596], eax
	mov eax, -85803555
	mov DWORD PTR [edi+600], eax
	mov eax, -771676715
	mov DWORD PTR [edi+604], eax
	mov eax, 1515612558
	mov DWORD PTR [edi+608], eax
	mov eax, -308998450
	mov DWORD PTR [edi+612], eax
	mov eax, -1989768032
	mov DWORD PTR [edi+616], eax
	mov eax, 1710507947
	mov DWORD PTR [edi+620], eax
	mov eax, 1896990689
	mov DWORD PTR [edi+624], eax
	mov eax, 794552114
	mov DWORD PTR [edi+628], eax
	mov eax, 231
	mov DWORD PTR [edi+632], eax
	mov eax, 0
	mov DWORD PTR [edi+636], eax
	mov eax, -2119319295
	mov DWORD PTR [edi+640], eax
	mov eax, -1288593053
	mov DWORD PTR [edi+644], eax
	mov eax, 417428190
	mov DWORD PTR [edi+648], eax
	mov eax, 1308409663
	mov DWORD PTR [edi+652], eax
	mov eax, -524110559
	mov DWORD PTR [edi+656], eax
	mov eax, 1863951449
	mov DWORD PTR [edi+660], eax
	mov eax, -1814986796
	mov DWORD PTR [edi+664], eax
	mov eax, -1803612448
	mov DWORD PTR [edi+668], eax
	mov eax, 1006105516
	mov DWORD PTR [edi+672], eax
	mov eax, -581917265
	mov DWORD PTR [edi+676], eax
	mov eax, -1338661218
	mov DWORD PTR [edi+680], eax
	mov eax, -1862527913
	mov DWORD PTR [edi+684], eax
	mov eax, -1669160998
	mov DWORD PTR [edi+688], eax
	mov eax, 558772800
	mov DWORD PTR [edi+692], eax
	mov eax, -1290679590
	mov DWORD PTR [edi+696], eax
	mov eax, -422633627
	mov DWORD PTR [edi+700], eax
	mov eax, 116
	mov DWORD PTR [edi+704], eax
	mov eax, 0
	mov DWORD PTR [edi+708], eax
	mov eax, 1520313998
	mov DWORD PTR [edi+712], eax
	mov eax, 675679818
	mov DWORD PTR [edi+716], eax
	mov eax, 995092659
	mov DWORD PTR [edi+720], eax
	mov eax, 541351754
	mov DWORD PTR [edi+724], eax
	mov eax, 1129396577
	mov DWORD PTR [edi+728], eax
	mov eax, -1332044232
	mov DWORD PTR [edi+732], eax
	mov eax, -2137008509
	mov DWORD PTR [edi+736], eax
	mov eax, 543336540
	mov DWORD PTR [edi+740], eax
	mov eax, 1286568467
	mov DWORD PTR [edi+744], eax
	mov eax, 374077241
	mov DWORD PTR [edi+748], eax
	mov eax, -1953259725
	mov DWORD PTR [edi+752], eax
	mov eax, 873191390
	mov DWORD PTR [edi+756], eax
	mov eax, 615239074
	mov DWORD PTR [edi+760], eax
	mov eax, -322143582
	mov DWORD PTR [edi+764], eax
	mov eax, -636076403
	mov DWORD PTR [edi+768], eax
	mov eax, 36586799
	mov DWORD PTR [edi+772], eax
	mov eax, 480
	mov DWORD PTR [edi+776], eax
	mov eax, 0
	mov DWORD PTR [edi+780], eax
	mov eax, -820650748
	mov DWORD PTR [edi+784], eax
	mov eax, 326946893
	mov DWORD PTR [edi+788], eax
	mov eax, -447447389
	mov DWORD PTR [edi+792], eax
	mov eax, -150488356
	mov DWORD PTR [edi+796], eax
	mov eax, 2034594815
	mov DWORD PTR [edi+800], eax
	mov eax, 312970552
	mov DWORD PTR [edi+804], eax
	mov eax, 1475829254
	mov DWORD PTR [edi+808], eax
	mov eax, -747495691
	mov DWORD PTR [edi+812], eax
	mov eax, 776587227
	mov DWORD PTR [edi+816], eax
	mov eax, -579984424
	mov DWORD PTR [edi+820], eax
	mov eax, -1217040834
	mov DWORD PTR [edi+824], eax
	mov eax, -806104766
	mov DWORD PTR [edi+828], eax
	mov eax, -1461360708
	mov DWORD PTR [edi+832], eax
	mov eax, 1540124001
	mov DWORD PTR [edi+836], eax
	mov eax, 1227689285
	mov DWORD PTR [edi+840], eax
	mov eax, 764281809
	mov DWORD PTR [edi+844], eax
	mov eax, 61
	mov DWORD PTR [edi+848], eax
	mov eax, 0
	mov DWORD PTR [edi+852], eax
	mov eax, 0
	mov DWORD PTR [edi+856], eax
	mov eax, -75497472
	mov DWORD PTR [edi+860], eax
	mov eax, 1891066829
	mov DWORD PTR [edi+864], eax
	mov eax, 681723940
	mov DWORD PTR [edi+868], eax
	mov eax, 599470556
	mov DWORD PTR [edi+872], eax
	mov eax, 400696603
	mov DWORD PTR [edi+876], eax
	mov eax, 1535408941
	mov DWORD PTR [edi+880], eax
	mov eax, -901768705
	mov DWORD PTR [edi+884], eax
	mov eax, 1042311220
	mov DWORD PTR [edi+888], eax
	mov eax, 47660220
	mov DWORD PTR [edi+892], eax
	mov eax, 0
	mov DWORD PTR [edi+896], eax
	mov eax, 0
	mov DWORD PTR [edi+900], eax
	mov eax, 0
	mov DWORD PTR [edi+904], eax
	mov eax, 0
	mov DWORD PTR [edi+908], eax
	mov eax, 0
	mov DWORD PTR [edi+912], eax
	mov eax, 0
	mov DWORD PTR [edi+916], eax
	mov eax, 0
	mov DWORD PTR [edi+920], eax
	mov eax, 0
	mov DWORD PTR [edi+924], eax
	mov eax, -3
	mov DWORD PTR [edi+928], eax
	mov eax, -1
	mov DWORD PTR [edi+932], eax
	mov eax, -1
	mov DWORD PTR [edi+936], eax
	mov eax, -1
	mov DWORD PTR [edi+940], eax
	mov eax, -1
	mov DWORD PTR [edi+944], eax
	mov eax, -1
	mov DWORD PTR [edi+948], eax
	mov eax, -1
	mov DWORD PTR [edi+952], eax
	mov eax, -1
	mov DWORD PTR [edi+956], eax
	mov eax, -1
	mov DWORD PTR [edi+960], eax
	mov eax, -1
	mov DWORD PTR [edi+964], eax
	mov eax, -1
	mov DWORD PTR [edi+968], eax
	mov eax, -1
	mov DWORD PTR [edi+972], eax
	mov eax, -1
	mov DWORD PTR [edi+976], eax
	mov eax, -1
	mov DWORD PTR [edi+980], eax
	mov eax, -1
	mov DWORD PTR [edi+984], eax
	mov eax, -1
	mov DWORD PTR [edi+988], eax
	mov eax, 511
	mov DWORD PTR [edi+992], eax
	mov eax, 0
	mov DWORD PTR [edi+996], eax
	mov eax, -1858575353
	mov DWORD PTR [edi+1000], eax
	mov eax, -1150306530
	mov DWORD PTR [edi+1004], eax
	mov eax, -1986246738
	mov DWORD PTR [edi+1008], eax
	mov eax, 1001769400
	mov DWORD PTR [edi+1012], eax
	mov eax, -150362672
	mov DWORD PTR [edi+1016], eax
	mov eax, 2144076104
	mov DWORD PTR [edi+1020], eax
	mov eax, -1087400341
	mov DWORD PTR [edi+1024], eax
	mov eax, 1367771011
	mov DWORD PTR [edi+1028], eax
	mov eax, -6
	mov DWORD PTR [edi+1032], eax
	mov eax, -1
	mov DWORD PTR [edi+1036], eax
	mov eax, -1
	mov DWORD PTR [edi+1040], eax
	mov eax, -1
	mov DWORD PTR [edi+1044], eax
	mov eax, -1
	mov DWORD PTR [edi+1048], eax
	mov eax, -1
	mov DWORD PTR [edi+1052], eax
	mov eax, -1
	mov DWORD PTR [edi+1056], eax
	mov eax, -1
	mov DWORD PTR [edi+1060], eax
	mov eax, 511
	mov DWORD PTR [edi+1064], eax
	mov eax, 0
	mov DWORD PTR [edi+1068], eax
	mov eax, 0
	mov DWORD PTR [edi+1072], eax
	mov eax, 0
	mov DWORD PTR [edi+1076], eax
	mov eax, 0
	mov DWORD PTR [edi+1080], eax
	mov eax, 0
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
	mov eax, 8388608
	mov DWORD PTR [edi+1148], eax
	mov eax, 0
	mov DWORD PTR [edi+1152], eax
	mov eax, 0
	mov DWORD PTR [edi+1156], eax
	mov eax, 0
	mov DWORD PTR [edi+1160], eax
	mov eax, 0
	mov DWORD PTR [edi+1164], eax
	mov eax, 0
	mov DWORD PTR [edi+1168], eax
	mov eax, 0
	mov DWORD PTR [edi+1172], eax
	mov eax, 0
	mov DWORD PTR [edi+1176], eax
	mov eax, 0
	mov DWORD PTR [edi+1180], eax
	mov eax, 0
	mov DWORD PTR [edi+1184], eax
	mov eax, 0
	mov DWORD PTR [edi+1188], eax
	mov eax, 0
	mov DWORD PTR [edi+1192], eax
	mov eax, 0
	mov DWORD PTR [edi+1196], eax
	mov eax, 0
	mov DWORD PTR [edi+1200], eax
	mov eax, 0
	mov DWORD PTR [edi+1204], eax
	mov eax, 0
	mov DWORD PTR [edi+1208], eax
	mov eax, 0
	mov DWORD PTR [edi+1212], eax
	mov eax, 0
	mov DWORD PTR [edi+1216], eax
	mov eax, 0
	mov DWORD PTR [edi+1220], eax
	mov eax, 0
	mov DWORD PTR [edi+1224], eax
	mov eax, 0
	mov DWORD PTR [edi+1228], eax
	mov eax, 0
	mov DWORD PTR [edi+1232], eax
	mov eax, 0
	mov DWORD PTR [edi+1236], eax
	mov eax, 0
	mov DWORD PTR [edi+1240], eax
	mov eax, 0
	mov DWORD PTR [edi+1244], eax
	mov eax, 0
	mov DWORD PTR [edi+1248], eax
	mov eax, 0
	mov DWORD PTR [edi+1252], eax
	mov eax, 0
	mov DWORD PTR [edi+1256], eax
	mov eax, 0
	mov DWORD PTR [edi+1260], eax
	mov eax, 0
	mov DWORD PTR [edi+1264], eax
	mov eax, 0
	mov DWORD PTR [edi+1268], eax
	mov eax, 0
	mov DWORD PTR [edi+1272], eax
	mov eax, 0
	mov DWORD PTR [edi+1276], eax
	mov eax, 0
	mov DWORD PTR [edi+1280], eax
	mov eax, 0
	mov DWORD PTR [edi+1284], eax
	mov eax, -1
	mov DWORD PTR [edi+3232], eax
	mov eax, 0
	mov DWORD PTR [edi+2872], eax
	mov eax, 0
	mov DWORD PTR [edi+2876], eax
	mov eax, 0
	mov DWORD PTR [edi+2880], eax
	mov eax, 16384
	mov DWORD PTR [edi+2884], eax
	mov eax, 0
	mov DWORD PTR [edi+2888], eax
	mov eax, 0
	mov DWORD PTR [edi+2892], eax
	mov eax, 0
	mov DWORD PTR [edi+2896], eax
	mov eax, 0
	mov DWORD PTR [edi+2900], eax
	mov eax, 0
	mov DWORD PTR [edi+2904], eax
	mov eax, 0
	mov DWORD PTR [edi+2908], eax
	mov eax, 0
	mov DWORD PTR [edi+2912], eax
	mov eax, 0
	mov DWORD PTR [edi+2916], eax
	mov eax, 0
	mov DWORD PTR [edi+2920], eax
	mov eax, 0
	mov DWORD PTR [edi+2924], eax
	mov eax, 0
	mov DWORD PTR [edi+2928], eax
	mov eax, 0
	mov DWORD PTR [edi+2932], eax
	mov eax, 0
	mov DWORD PTR [edi+2936], eax
	mov eax, 0
	mov DWORD PTR [edi+2940], eax
	mov eax, -1369939065
	mov DWORD PTR [edi+2944], eax
	mov eax, -2146146993
	mov DWORD PTR [edi+2948], eax
	mov eax, -365582305
	mov DWORD PTR [edi+2952], eax
	mov eax, 2029494927
	mov DWORD PTR [edi+2956], eax
	mov eax, -1004628454
	mov DWORD PTR [edi+2960], eax
	mov eax, -2087011857
	mov DWORD PTR [edi+2964], eax
	mov eax, 1587402975
	mov DWORD PTR [edi+2968], eax
	mov eax, -1114953376
	mov DWORD PTR [edi+2972], eax
	mov eax, -1460256951
	mov DWORD PTR [edi+2976], eax
	mov eax, -257225572
	mov DWORD PTR [edi+2980], eax
	mov eax, -926451580
	mov DWORD PTR [edi+2984], eax
	mov eax, -102999484
	mov DWORD PTR [edi+2988], eax
	mov eax, 768399754
	mov DWORD PTR [edi+2992], eax
	mov eax, 2001825081
	mov DWORD PTR [edi+2996], eax
	mov eax, -799325536
	mov DWORD PTR [edi+3000], eax
	mov eax, 264850704
	mov DWORD PTR [edi+3004], eax
	mov eax, 77
	mov DWORD PTR [edi+3008], eax
	mov eax, 0
	mov DWORD PTR [edi+3012], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2492], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2504], eax
	mov eax, 0
	mov DWORD PTR [edi+2508], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	mov DWORD PTR [edi+2368], edx
	or edx, 1
	xor edx, 3
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov edx, DWORD PTR [edi+2440]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+2444]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+2448]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+2452]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+2456]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+2460]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+2464]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+2468]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+2472]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+2476]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+2480]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+2484]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+2488]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+2492]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+2496]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+2500]
	sbb edx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+2504]
	sbb edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+2508]
	sbb edx, DWORD PTR [edi+132]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov eax, 2872
	mov ecx, 2440
	mov edx, 2512
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2512
	mov ecx, 2512
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2512
	mov ecx, 3016
	mov edx, 3088
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2512
	mov ecx, 496
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3016
	mov ecx, 3088
	mov edx, 2800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2944
	mov ecx, 2800
	mov edx, 3088
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [edi+928], eax
	mov eax, 0
	mov DWORD PTR [edi+932], eax
	mov eax, 0
	mov DWORD PTR [edi+936], eax
	mov eax, 0
	mov DWORD PTR [edi+940], eax
	mov eax, 0
	mov DWORD PTR [edi+944], eax
	mov eax, 0
	mov DWORD PTR [edi+948], eax
	mov eax, 0
	mov DWORD PTR [edi+952], eax
	mov eax, 0
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
	mov eax, 128
	mov DWORD PTR [edi+992], eax
	mov eax, 0
	mov DWORD PTR [edi+996], eax
	mov esi, 72
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+928]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+5256], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+5257], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+5258], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+5259], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+5260], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+5261], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+5262], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+5263], dl
	test esi, esi
	jne 20b
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+448]
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+452]
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+456]
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+460]
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+464]
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+468]
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+2220], eax
	mov esi, 576
21:
	sub esi, 1
	mov eax, 2152
	mov ecx, 2152
	mov edx, 2152
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3088
	mov ecx, 2152
	mov edx, 2224
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+5256]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+2152]
	mov edx, DWORD PTR [edi+2224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+2156]
	mov edx, DWORD PTR [edi+2228]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+2160]
	mov edx, DWORD PTR [edi+2232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+2164]
	mov edx, DWORD PTR [edi+2236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+2168]
	mov edx, DWORD PTR [edi+2240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+2172]
	mov edx, DWORD PTR [edi+2244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+2176]
	mov edx, DWORD PTR [edi+2248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+2180]
	mov edx, DWORD PTR [edi+2252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+2184]
	mov edx, DWORD PTR [edi+2256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+2188]
	mov edx, DWORD PTR [edi+2260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+2192]
	mov edx, DWORD PTR [edi+2264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+2196]
	mov edx, DWORD PTR [edi+2268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+2200]
	mov edx, DWORD PTR [edi+2272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+2204]
	mov edx, DWORD PTR [edi+2276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+2208]
	mov edx, DWORD PTR [edi+2280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+2212]
	mov edx, DWORD PTR [edi+2284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+2216]
	mov edx, DWORD PTR [edi+2288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+2220]
	mov edx, DWORD PTR [edi+2292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2220], eax
	test esi, esi
	jne 21b
	mov eax, 352
	mov ecx, 2152
	mov edx, 2656
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2656
	mov ecx, 280
	mov edx, 2728
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2656]
	mov ecx, DWORD PTR [edi+2368]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov eax, DWORD PTR [edi+2656]
	mov edx, DWORD PTR [edi+2728]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2656], eax
	mov eax, DWORD PTR [edi+2660]
	mov edx, DWORD PTR [edi+2732]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2660], eax
	mov eax, DWORD PTR [edi+2664]
	mov edx, DWORD PTR [edi+2736]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2664], eax
	mov eax, DWORD PTR [edi+2668]
	mov edx, DWORD PTR [edi+2740]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2668], eax
	mov eax, DWORD PTR [edi+2672]
	mov edx, DWORD PTR [edi+2744]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2672], eax
	mov eax, DWORD PTR [edi+2676]
	mov edx, DWORD PTR [edi+2748]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2676], eax
	mov eax, DWORD PTR [edi+2680]
	mov edx, DWORD PTR [edi+2752]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2680], eax
	mov eax, DWORD PTR [edi+2684]
	mov edx, DWORD PTR [edi+2756]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2684], eax
	mov eax, DWORD PTR [edi+2688]
	mov edx, DWORD PTR [edi+2760]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2688], eax
	mov eax, DWORD PTR [edi+2692]
	mov edx, DWORD PTR [edi+2764]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2692], eax
	mov eax, DWORD PTR [edi+2696]
	mov edx, DWORD PTR [edi+2768]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2696], eax
	mov eax, DWORD PTR [edi+2700]
	mov edx, DWORD PTR [edi+2772]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2700], eax
	mov eax, DWORD PTR [edi+2704]
	mov edx, DWORD PTR [edi+2776]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [edi+2708]
	mov edx, DWORD PTR [edi+2780]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2708], eax
	mov eax, DWORD PTR [edi+2712]
	mov edx, DWORD PTR [edi+2784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+2716]
	mov edx, DWORD PTR [edi+2788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+2720]
	mov edx, DWORD PTR [edi+2792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+2724]
	mov edx, DWORD PTR [edi+2796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2724], eax
	mov eax, 2872
	mov ecx, 2656
	mov edx, 2584
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2584
	mov ecx, 2584
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3088
	mov ecx, 3016
	mov edx, 2800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+2800]
	or edx, DWORD PTR [edi+2804]
	or edx, DWORD PTR [edi+2808]
	or edx, DWORD PTR [edi+2812]
	or edx, DWORD PTR [edi+2816]
	or edx, DWORD PTR [edi+2820]
	or edx, DWORD PTR [edi+2824]
	or edx, DWORD PTR [edi+2828]
	or edx, DWORD PTR [edi+2832]
	or edx, DWORD PTR [edi+2836]
	or edx, DWORD PTR [edi+2840]
	or edx, DWORD PTR [edi+2844]
	or edx, DWORD PTR [edi+2848]
	or edx, DWORD PTR [edi+2852]
	or edx, DWORD PTR [edi+2856]
	or edx, DWORD PTR [edi+2860]
	or edx, DWORD PTR [edi+2864]
	or edx, DWORD PTR [edi+2868]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+2656]
	mov ecx, DWORD PTR [edi+2368]
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
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov ecx, DWORD PTR [edi+3232]
	mov ebx, DWORD PTR [esp+4]
	mov eax, 4
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+2440]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+63], eax
	mov eax, DWORD PTR [edi+2444]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+59], eax
	mov eax, DWORD PTR [edi+2448]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+55], eax
	mov eax, DWORD PTR [edi+2452]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+51], eax
	mov eax, DWORD PTR [edi+2456]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+47], eax
	mov eax, DWORD PTR [edi+2460]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+43], eax
	mov eax, DWORD PTR [edi+2464]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+39], eax
	mov eax, DWORD PTR [edi+2468]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+35], eax
	mov eax, DWORD PTR [edi+2472]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+31], eax
	mov eax, DWORD PTR [edi+2476]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+27], eax
	mov eax, DWORD PTR [edi+2480]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+23], eax
	mov eax, DWORD PTR [edi+2484]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+19], eax
	mov eax, DWORD PTR [edi+2488]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+15], eax
	mov eax, DWORD PTR [edi+2492]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+11], eax
	mov eax, DWORD PTR [edi+2496]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+7], eax
	mov eax, DWORD PTR [edi+2500]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+3], eax
	mov eax, DWORD PTR [edi+2504]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [ebx+1], dl
	mov edx, eax
	mov BYTE PTR [ebx+2], dl
	mov eax, DWORD PTR [edi+2656]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+129], eax
	mov eax, DWORD PTR [edi+2660]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+125], eax
	mov eax, DWORD PTR [edi+2664]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+121], eax
	mov eax, DWORD PTR [edi+2668]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+117], eax
	mov eax, DWORD PTR [edi+2672]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+113], eax
	mov eax, DWORD PTR [edi+2676]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+109], eax
	mov eax, DWORD PTR [edi+2680]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+105], eax
	mov eax, DWORD PTR [edi+2684]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+101], eax
	mov eax, DWORD PTR [edi+2688]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+97], eax
	mov eax, DWORD PTR [edi+2692]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+93], eax
	mov eax, DWORD PTR [edi+2696]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+89], eax
	mov eax, DWORD PTR [edi+2700]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+85], eax
	mov eax, DWORD PTR [edi+2704]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+81], eax
	mov eax, DWORD PTR [edi+2708]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+77], eax
	mov eax, DWORD PTR [edi+2712]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+73], eax
	mov eax, DWORD PTR [edi+2716]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+69], eax
	mov eax, DWORD PTR [edi+2720]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [ebx+67], dl
	mov edx, eax
	mov BYTE PTR [ebx+68], dl
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
