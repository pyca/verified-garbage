// The functions of `src/ecdsa_p521.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_verify:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+12]
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
	mov eax, DWORD PTR [edi+2368]
	shr eax, 7
	mov edx, DWORD PTR [edi+2372]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [edi+2372]
	shr eax, 7
	mov edx, DWORD PTR [edi+2376]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [edi+2376]
	shr eax, 7
	mov edx, DWORD PTR [edi+2380]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [edi+2380]
	shr eax, 7
	mov edx, DWORD PTR [edi+2384]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [edi+2384]
	shr eax, 7
	mov edx, DWORD PTR [edi+2388]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [edi+2388]
	shr eax, 7
	mov edx, DWORD PTR [edi+2392]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [edi+2392]
	shr eax, 7
	mov edx, DWORD PTR [edi+2396]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [edi+2396]
	shr eax, 7
	mov edx, DWORD PTR [edi+2400]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [edi+2400]
	shr eax, 7
	mov edx, DWORD PTR [edi+2404]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [edi+2404]
	shr eax, 7
	mov edx, DWORD PTR [edi+2408]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [edi+2408]
	shr eax, 7
	mov edx, DWORD PTR [edi+2412]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [edi+2412]
	shr eax, 7
	mov edx, DWORD PTR [edi+2416]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [edi+2416]
	shr eax, 7
	mov edx, DWORD PTR [edi+2420]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [edi+2420]
	shr eax, 7
	mov edx, DWORD PTR [edi+2424]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [edi+2424]
	shr eax, 7
	mov edx, DWORD PTR [edi+2428]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [edi+2428]
	shr eax, 7
	mov edx, DWORD PTR [edi+2432]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2428], eax
	mov eax, DWORD PTR [edi+2432]
	shr eax, 7
	mov edx, DWORD PTR [edi+2436]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2432], eax
	mov eax, DWORD PTR [edi+2436]
	shr eax, 7
	mov DWORD PTR [edi+2436], eax
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
	mov esi, 72
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+2296]
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
	mov esi, 72
21:
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
	mov BYTE PTR [ebx+4676], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4677], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4678], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4679], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4680], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4681], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4682], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4683], dl
	test esi, esi
	jne 21b
	mov esi, 72
22:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+1000]
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
	jne 22b
	mov ebx, DWORD PTR [esp+12]
	add ebx, 66
	mov eax, DWORD PTR [ebx+62]
	bswap eax
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [ebx+58]
	bswap eax
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [ebx+54]
	bswap eax
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [ebx+50]
	bswap eax
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [ebx+46]
	bswap eax
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [ebx+42]
	bswap eax
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [ebx+38]
	bswap eax
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [ebx+34]
	bswap eax
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [ebx+30]
	bswap eax
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [ebx+26]
	bswap eax
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [ebx+22]
	bswap eax
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [ebx+18]
	bswap eax
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [ebx+14]
	bswap eax
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [ebx+10]
	bswap eax
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [ebx+6]
	bswap eax
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [ebx+2]
	bswap eax
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2288], eax
	mov eax, 0
	mov DWORD PTR [edi+2292], eax
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
	mov ebx, DWORD PTR [esp+4]
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
	mov ebx, DWORD PTR [esp+4]
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
	mov edx, DWORD PTR [edi+2296]
	sub edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+2300]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+2304]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+2308]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+2312]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+2316]
	sbb edx, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+2320]
	sbb edx, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+2324]
	sbb edx, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+2328]
	sbb edx, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+2332]
	sbb edx, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+2336]
	sbb edx, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+2340]
	sbb edx, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+2344]
	sbb edx, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+2348]
	sbb edx, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+2352]
	sbb edx, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+2356]
	sbb edx, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+2360]
	sbb edx, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+2364]
	sbb edx, DWORD PTR [edi+204]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+2296]
	or edx, DWORD PTR [edi+2300]
	or edx, DWORD PTR [edi+2304]
	or edx, DWORD PTR [edi+2308]
	or edx, DWORD PTR [edi+2312]
	or edx, DWORD PTR [edi+2316]
	or edx, DWORD PTR [edi+2320]
	or edx, DWORD PTR [edi+2324]
	or edx, DWORD PTR [edi+2328]
	or edx, DWORD PTR [edi+2332]
	or edx, DWORD PTR [edi+2336]
	or edx, DWORD PTR [edi+2340]
	or edx, DWORD PTR [edi+2344]
	or edx, DWORD PTR [edi+2348]
	or edx, DWORD PTR [edi+2352]
	or edx, DWORD PTR [edi+2356]
	or edx, DWORD PTR [edi+2360]
	or edx, DWORD PTR [edi+2364]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov edx, DWORD PTR [edi+2224]
	sub edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+2228]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+2232]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+2236]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+2240]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+2244]
	sbb edx, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+2248]
	sbb edx, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+2252]
	sbb edx, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+2256]
	sbb edx, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+2260]
	sbb edx, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+2264]
	sbb edx, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+2268]
	sbb edx, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+2272]
	sbb edx, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+2276]
	sbb edx, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+2280]
	sbb edx, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+2284]
	sbb edx, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+2288]
	sbb edx, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+2292]
	sbb edx, DWORD PTR [edi+204]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+2224]
	or edx, DWORD PTR [edi+2228]
	or edx, DWORD PTR [edi+2232]
	or edx, DWORD PTR [edi+2236]
	or edx, DWORD PTR [edi+2240]
	or edx, DWORD PTR [edi+2244]
	or edx, DWORD PTR [edi+2248]
	or edx, DWORD PTR [edi+2252]
	or edx, DWORD PTR [edi+2256]
	or edx, DWORD PTR [edi+2260]
	or edx, DWORD PTR [edi+2264]
	or edx, DWORD PTR [edi+2268]
	or edx, DWORD PTR [edi+2272]
	or edx, DWORD PTR [edi+2276]
	or edx, DWORD PTR [edi+2280]
	or edx, DWORD PTR [edi+2284]
	or edx, DWORD PTR [edi+2288]
	or edx, DWORD PTR [edi+2292]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov eax, 784
	mov ecx, 2224
	mov edx, 2728
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [edi+2220], eax
	mov esi, 576
23:
	sub esi, 1
	mov eax, 2152
	mov ecx, 2152
	mov edx, 2152
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2728
	mov ecx, 2152
	mov edx, 2224
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
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
	jne 23b
	mov eax, 784
	mov ecx, 2368
	mov edx, 2944
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 2296
	mov edx, 2872
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2152
	mov ecx, 2944
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2152
	mov ecx, 2872
	mov edx, 3088
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 352
	mov ecx, 3016
	mov edx, 2512
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 352
	mov ecx, 3088
	mov edx, 2584
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+2512]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [edi+2516]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [edi+2520]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [edi+2524]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [edi+2528]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [edi+2532]
	mov DWORD PTR [edi+2316], eax
	mov eax, DWORD PTR [edi+2536]
	mov DWORD PTR [edi+2320], eax
	mov eax, DWORD PTR [edi+2540]
	mov DWORD PTR [edi+2324], eax
	mov eax, DWORD PTR [edi+2544]
	mov DWORD PTR [edi+2328], eax
	mov eax, DWORD PTR [edi+2548]
	mov DWORD PTR [edi+2332], eax
	mov eax, DWORD PTR [edi+2552]
	mov DWORD PTR [edi+2336], eax
	mov eax, DWORD PTR [edi+2556]
	mov DWORD PTR [edi+2340], eax
	mov eax, DWORD PTR [edi+2560]
	mov DWORD PTR [edi+2344], eax
	mov eax, DWORD PTR [edi+2564]
	mov DWORD PTR [edi+2348], eax
	mov eax, DWORD PTR [edi+2568]
	mov DWORD PTR [edi+2352], eax
	mov eax, DWORD PTR [edi+2572]
	mov DWORD PTR [edi+2356], eax
	mov eax, DWORD PTR [edi+2576]
	mov DWORD PTR [edi+2360], eax
	mov eax, DWORD PTR [edi+2580]
	mov DWORD PTR [edi+2364], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+672]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+676]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+680]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+684]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+688]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+692]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+1212], eax
	push edi
	call {vg_p521_mul}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [edi+3016], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [edi+3020], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [edi+3024], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [edi+3028], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+3032], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+3036], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+3040], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+3044], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+3048], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+3052], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+3056], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+3060], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+3064], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+3068], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+3072], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+3076], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+3080], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+3084], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+3088], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+3092], eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+3096], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+3100], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+3104], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+3108], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+3112], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+3116], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+3120], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+3124], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+3128], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+3132], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+3136], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+3140], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [edi+3144], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [edi+3148], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [edi+3152], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [edi+3156], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+2728], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+2732], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+2736], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+2740], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+2744], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+2748], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+2796], eax
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
	mov eax, DWORD PTR [edi+2584]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [edi+2588]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [edi+2592]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [edi+2596]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [edi+2600]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [edi+2604]
	mov DWORD PTR [edi+2316], eax
	mov eax, DWORD PTR [edi+2608]
	mov DWORD PTR [edi+2320], eax
	mov eax, DWORD PTR [edi+2612]
	mov DWORD PTR [edi+2324], eax
	mov eax, DWORD PTR [edi+2616]
	mov DWORD PTR [edi+2328], eax
	mov eax, DWORD PTR [edi+2620]
	mov DWORD PTR [edi+2332], eax
	mov eax, DWORD PTR [edi+2624]
	mov DWORD PTR [edi+2336], eax
	mov eax, DWORD PTR [edi+2628]
	mov DWORD PTR [edi+2340], eax
	mov eax, DWORD PTR [edi+2632]
	mov DWORD PTR [edi+2344], eax
	mov eax, DWORD PTR [edi+2636]
	mov DWORD PTR [edi+2348], eax
	mov eax, DWORD PTR [edi+2640]
	mov DWORD PTR [edi+2352], eax
	mov eax, DWORD PTR [edi+2644]
	mov DWORD PTR [edi+2356], eax
	mov eax, DWORD PTR [edi+2648]
	mov DWORD PTR [edi+2360], eax
	mov eax, DWORD PTR [edi+2652]
	mov DWORD PTR [edi+2364], eax
	mov eax, DWORD PTR [edi+2800]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+2804]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+2808]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+2812]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+2816]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+2820]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+2824]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+2828]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+2832]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+2836]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+2840]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+2844]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+2848]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+2852]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+2856]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+2860]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+2864]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+2868]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+3160]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+3164]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+3168]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+3172]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+3176]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+3180]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+3184]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+3188]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+3192]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+3196]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+3200]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+3204]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+3208]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+3212]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+3216]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+3220]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+3224]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+3228]
	mov DWORD PTR [edi+1212], eax
	push edi
	call {vg_p521_mul}
	pop eax
	mov edi, DWORD PTR [esp+16]
	mov eax, 1072
	mov ecx, 3016
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 3088
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 2728
	mov edx, 1864
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
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1144
	mov ecx, 1072
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1720
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1936
	mov edx, 1936
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2728
	mov ecx, 3016
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1072
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2728
	mov ecx, 3088
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1144
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 2080
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 496
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 568
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1288
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1792
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1792
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 1288
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1720
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 568
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 1720
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 496
	mov edx, 1864
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1864
	mov ecx, 2008
	mov edx, 2008
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 1792
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1360
	mov edx, 1360
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2008
	mov ecx, 2080
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1288
	mov ecx, 1936
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1288
	mov edx, 1288
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1936
	mov edx, 1720
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1432
	mov ecx, 2080
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1720
	mov ecx, 1432
	mov edx, 1432
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1328]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1332]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1336]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1340]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1344]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1348]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1352]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1356]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1360]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1364]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+1368]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1372]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1376]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1380]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [edi+1384]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1388]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1392]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1396]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [edi+1400]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1404]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1408]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1412]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [edi+1416]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+1420]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+1424]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+1428]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [edi+1432]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1436]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1440]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1444]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [edi+1448]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1452]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1456]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1460]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [edi+1464]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1468]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1472]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1476]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [edi+1480]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+1484]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+1488]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+1492]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [edi+1496]
	mov DWORD PTR [edi+1280], eax
	mov eax, DWORD PTR [edi+1500]
	mov DWORD PTR [edi+1284], eax
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
24:
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
	mov eax, 1216
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
	movzx eax, BYTE PTR [eax+4676]
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
	jne 24b
	mov eax, 2152
	mov ecx, 1072
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
	mov eax, 352
	mov ecx, 2512
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
	mov eax, 784
	mov ecx, 2584
	mov edx, 2800
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2872
	mov ecx, 2800
	mov edx, 2944
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1216]
	or edx, DWORD PTR [edi+1220]
	or edx, DWORD PTR [edi+1224]
	or edx, DWORD PTR [edi+1228]
	or edx, DWORD PTR [edi+1232]
	or edx, DWORD PTR [edi+1236]
	or edx, DWORD PTR [edi+1240]
	or edx, DWORD PTR [edi+1244]
	or edx, DWORD PTR [edi+1248]
	or edx, DWORD PTR [edi+1252]
	or edx, DWORD PTR [edi+1256]
	or edx, DWORD PTR [edi+1260]
	or edx, DWORD PTR [edi+1264]
	or edx, DWORD PTR [edi+1268]
	or edx, DWORD PTR [edi+1272]
	or edx, DWORD PTR [edi+1276]
	or edx, DWORD PTR [edi+1280]
	or edx, DWORD PTR [edi+1284]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov edx, DWORD PTR [edi+2944]
	or edx, DWORD PTR [edi+2948]
	or edx, DWORD PTR [edi+2952]
	or edx, DWORD PTR [edi+2956]
	or edx, DWORD PTR [edi+2960]
	or edx, DWORD PTR [edi+2964]
	or edx, DWORD PTR [edi+2968]
	or edx, DWORD PTR [edi+2972]
	or edx, DWORD PTR [edi+2976]
	or edx, DWORD PTR [edi+2980]
	or edx, DWORD PTR [edi+2984]
	or edx, DWORD PTR [edi+2988]
	or edx, DWORD PTR [edi+2992]
	or edx, DWORD PTR [edi+2996]
	or edx, DWORD PTR [edi+3000]
	or edx, DWORD PTR [edi+3004]
	or edx, DWORD PTR [edi+3008]
	or edx, DWORD PTR [edi+3012]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov ecx, DWORD PTR [edi+3232]
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6

vg_ecdsa_p521_sign:
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
	mov DWORD PTR [esp+230], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+234], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+238], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+242], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+301], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+305], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+309], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+313], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2417], eax
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
	mov ecx, 165
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
	mov eax, 293
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2417], eax
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
	mov ecx, 165
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
	mov eax, 293
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
	mov eax, 8
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
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+416], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+420], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+424], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+428], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+432], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
	mov DWORD PTR [esp+234], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+238], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+242], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+305], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+309], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+313], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+258]
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+258]
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
	mov eax, 8
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
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
	mov DWORD PTR [esp+198], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+202], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+206], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+210], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+214], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+218], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+222], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+226], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [esp+230], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [esp+234], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [esp+238], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [esp+242], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+269], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+273], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+277], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+281], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+285], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+289], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+293], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+297], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [esp+301], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [esp+305], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [esp+309], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [esp+313], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2419], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2423], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2427], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2431], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2435], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2439], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2443], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2447], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2449], eax
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
	mov ecx, 197
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
	mov eax, 325
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
	add ebx, 256
	mov eax, 192
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
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
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
	mov eax, 192
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
	add ebx, 256
	mov eax, 192
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
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2419], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2423], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2427], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2431], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2435], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2439], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2443], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2447], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2449], eax
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
	mov ecx, 197
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
	mov eax, 325
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
	add ebx, 256
	mov eax, 192
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
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
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
	mov eax, 192
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
	add ebx, 256
	mov eax, 192
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
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov eax, 8
	mov DWORD PTR [esp+176], eax
220:
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
	mov eax, 192
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
	add ebx, 256
	mov eax, 192
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
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
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
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+388], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+392], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+396], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+400], eax
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
	mov eax, 192
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
	add ebx, 256
	mov eax, 192
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
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+112], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+116], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+416], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+420], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+424], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+428], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+432], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+436], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [esp+440], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [esp+444], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [esp+448], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [esp+452], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [esp+456], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [esp+460], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp+464], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
	mov ecx, 65
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
	mov eax, 193
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
	add ebx, 256
	mov eax, 192
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
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esp+60], eax
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
	mov eax, 192
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
	add ebx, 256
	mov eax, 192
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
	mov DWORD PTR [esp+214], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+218], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+222], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+226], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+230], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+234], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+238], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+242], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+285], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+289], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+293], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+297], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+301], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+305], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+309], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+313], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2419], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2423], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2427], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2431], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2433], eax
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
	mov ecx, 181
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
	mov eax, 309
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2419], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2423], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2427], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2431], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2433], eax
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
	mov ecx, 181
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
	mov eax, 309
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
	mov eax, 8
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
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
	mov DWORD PTR [esp+230], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+234], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+238], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+242], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+301], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+305], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+309], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+313], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2417], eax
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
	mov ecx, 165
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
	mov eax, 229
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2415], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2417], eax
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
	mov ecx, 165
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
	mov eax, 229
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
	mov eax, 8
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
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+416], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+420], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+424], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+428], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+432], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
	mov DWORD PTR [esp+234], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+238], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+242], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+305], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+309], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+313], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+258]
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2407], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2411], eax
	mov eax, DWORD PTR [esp+258]
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
	mov eax, 8
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
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
	mov DWORD PTR [esp+242], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+313], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2339], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2343], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2405], eax
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
	mov ecx, 153
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
	mov eax, 217
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2339], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2343], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2403], eax
	mov eax, DWORD PTR [esp+258]
	mov DWORD PTR [edi+2405], eax
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
	mov ecx, 153
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
	mov eax, 217
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
	mov eax, 8
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
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
	mov DWORD PTR [esp+246], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+250], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+254], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+258], eax
	mov eax, 0
	mov DWORD PTR [esp+268], eax
	mov DWORD PTR [esp+272], eax
	mov DWORD PTR [esp+276], eax
	mov DWORD PTR [esp+280], eax
	mov DWORD PTR [esp+284], eax
	mov DWORD PTR [esp+288], eax
	mov DWORD PTR [esp+292], eax
	mov DWORD PTR [esp+296], eax
	mov DWORD PTR [esp+300], eax
	mov DWORD PTR [esp+304], eax
	mov DWORD PTR [esp+308], eax
	mov DWORD PTR [esp+312], eax
	mov DWORD PTR [esp+316], eax
	mov DWORD PTR [esp+320], eax
	mov DWORD PTR [esp+324], eax
	mov DWORD PTR [esp+328], eax
	mov DWORD PTR [esp+332], eax
	mov DWORD PTR [esp+336], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [esp+317], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [esp+321], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [esp+325], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [esp+329], eax
	mov esi, esp
	add esi, 268
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 1
	mov edx, DWORD PTR [edi+2564]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 1
	mov edx, DWORD PTR [edi+2568]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 1
	mov edx, DWORD PTR [edi+2572]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 1
	mov edx, DWORD PTR [edi+2576]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 1
	mov edx, DWORD PTR [edi+2580]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 1
	mov edx, DWORD PTR [edi+2584]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 1
	mov edx, DWORD PTR [edi+2588]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 1
	mov edx, DWORD PTR [edi+2592]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 1
	mov edx, DWORD PTR [edi+2596]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 1
	mov edx, DWORD PTR [edi+2600]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 1
	mov edx, DWORD PTR [edi+2604]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 1
	mov edx, DWORD PTR [edi+2608]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 1
	mov edx, DWORD PTR [edi+2612]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 1
	mov edx, DWORD PTR [edi+2616]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 1
	mov edx, DWORD PTR [edi+2620]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 1
	mov edx, DWORD PTR [edi+2624]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 1
	mov edx, DWORD PTR [edi+2628]
	and edx, 1
	ror edx, 1
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 1
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+330], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+326], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+322], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+318], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+314], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+310], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+306], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+302], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+298], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+294], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+290], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+286], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+282], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+278], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+274], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+270], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+268], dl
	mov edx, eax
	mov BYTE PTR [esp+269], dl
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2335], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2339], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2343], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+258]
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
	mov eax, DWORD PTR [esi+62]
	mov DWORD PTR [edi+2335], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2339], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2343], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2347], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2351], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2355], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2359], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2363], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2367], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2371], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2375], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2379], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2383], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2387], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2391], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2395], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2399], eax
	mov eax, DWORD PTR [esp+258]
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
	mov eax, 8
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
	mov DWORD PTR [esp+404], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+408], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+412], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+416], eax
	mov edi, DWORD PTR [esp+488]
	mov esi, esp
	add esi, 340
	mov eax, DWORD PTR [esi+62]
	bswap eax
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [esi+58]
	bswap eax
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [esi+54]
	bswap eax
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [esi+50]
	bswap eax
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [esi+46]
	bswap eax
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [esi+42]
	bswap eax
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [esi+38]
	bswap eax
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [esi+34]
	bswap eax
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [esi+30]
	bswap eax
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [esi+26]
	bswap eax
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [esi+22]
	bswap eax
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [esi+18]
	bswap eax
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [esi+14]
	bswap eax
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [esi+10]
	bswap eax
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [esi+6]
	bswap eax
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [esi+2]
	bswap eax
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	shr eax, 16
	mov DWORD PTR [edi+2624], eax
	mov eax, 0
	mov DWORD PTR [edi+2628], eax
	mov eax, DWORD PTR [edi+2560]
	shr eax, 7
	mov edx, DWORD PTR [edi+2564]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2560], eax
	mov eax, DWORD PTR [edi+2564]
	shr eax, 7
	mov edx, DWORD PTR [edi+2568]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2564], eax
	mov eax, DWORD PTR [edi+2568]
	shr eax, 7
	mov edx, DWORD PTR [edi+2572]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2568], eax
	mov eax, DWORD PTR [edi+2572]
	shr eax, 7
	mov edx, DWORD PTR [edi+2576]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2572], eax
	mov eax, DWORD PTR [edi+2576]
	shr eax, 7
	mov edx, DWORD PTR [edi+2580]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2576], eax
	mov eax, DWORD PTR [edi+2580]
	shr eax, 7
	mov edx, DWORD PTR [edi+2584]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2580], eax
	mov eax, DWORD PTR [edi+2584]
	shr eax, 7
	mov edx, DWORD PTR [edi+2588]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2584], eax
	mov eax, DWORD PTR [edi+2588]
	shr eax, 7
	mov edx, DWORD PTR [edi+2592]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2588], eax
	mov eax, DWORD PTR [edi+2592]
	shr eax, 7
	mov edx, DWORD PTR [edi+2596]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2592], eax
	mov eax, DWORD PTR [edi+2596]
	shr eax, 7
	mov edx, DWORD PTR [edi+2600]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2596], eax
	mov eax, DWORD PTR [edi+2600]
	shr eax, 7
	mov edx, DWORD PTR [edi+2604]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2600], eax
	mov eax, DWORD PTR [edi+2604]
	shr eax, 7
	mov edx, DWORD PTR [edi+2608]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2604], eax
	mov eax, DWORD PTR [edi+2608]
	shr eax, 7
	mov edx, DWORD PTR [edi+2612]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2608], eax
	mov eax, DWORD PTR [edi+2612]
	shr eax, 7
	mov edx, DWORD PTR [edi+2616]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2612], eax
	mov eax, DWORD PTR [edi+2616]
	shr eax, 7
	mov edx, DWORD PTR [edi+2620]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2616], eax
	mov eax, DWORD PTR [edi+2620]
	shr eax, 7
	mov edx, DWORD PTR [edi+2624]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2620], eax
	mov eax, DWORD PTR [edi+2624]
	shr eax, 7
	mov edx, DWORD PTR [edi+2628]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2624], eax
	mov eax, DWORD PTR [edi+2628]
	shr eax, 7
	mov DWORD PTR [edi+2628], eax
	mov ecx, -1
	mov eax, DWORD PTR [edi+2560]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+402], eax
	mov eax, DWORD PTR [edi+2564]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+398], eax
	mov eax, DWORD PTR [edi+2568]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+394], eax
	mov eax, DWORD PTR [edi+2572]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+390], eax
	mov eax, DWORD PTR [edi+2576]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+386], eax
	mov eax, DWORD PTR [edi+2580]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+382], eax
	mov eax, DWORD PTR [edi+2584]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+378], eax
	mov eax, DWORD PTR [edi+2588]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+374], eax
	mov eax, DWORD PTR [edi+2592]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+370], eax
	mov eax, DWORD PTR [edi+2596]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+366], eax
	mov eax, DWORD PTR [edi+2600]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+362], eax
	mov eax, DWORD PTR [edi+2604]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+358], eax
	mov eax, DWORD PTR [edi+2608]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+354], eax
	mov eax, DWORD PTR [edi+2612]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+350], eax
	mov eax, DWORD PTR [edi+2616]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+346], eax
	mov eax, DWORD PTR [edi+2620]
	and eax, ecx
	bswap eax
	mov DWORD PTR [esp+342], eax
	mov eax, DWORD PTR [edi+2624]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [esp+340], dl
	mov edx, eax
	mov BYTE PTR [esp+341], dl
	mov edi, DWORD PTR [esp+472]
	mov esi, DWORD PTR [esp+476]
	mov edx, esp
	add edx, 268
	mov ecx, esp
	add ecx, 340
	mov ebp, DWORD PTR [esp+488]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_p521_sign_k}
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
