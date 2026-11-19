// The functions of `src/internal/vg_ecdsa_p521_sign_k.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sign_k:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_P521_COMB}
	pop ecx
	mov edx, DWORD PTR [esp+20]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+16]
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
	mov ebx, DWORD PTR [esp+12]
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
	mov eax, DWORD PTR [edi+2440]
	shr eax, 7
	mov edx, DWORD PTR [edi+2444]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [edi+2444]
	shr eax, 7
	mov edx, DWORD PTR [edi+2448]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [edi+2448]
	shr eax, 7
	mov edx, DWORD PTR [edi+2452]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [edi+2452]
	shr eax, 7
	mov edx, DWORD PTR [edi+2456]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [edi+2456]
	shr eax, 7
	mov edx, DWORD PTR [edi+2460]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [edi+2460]
	shr eax, 7
	mov edx, DWORD PTR [edi+2464]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [edi+2464]
	shr eax, 7
	mov edx, DWORD PTR [edi+2468]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [edi+2468]
	shr eax, 7
	mov edx, DWORD PTR [edi+2472]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [edi+2472]
	shr eax, 7
	mov edx, DWORD PTR [edi+2476]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [edi+2476]
	shr eax, 7
	mov edx, DWORD PTR [edi+2480]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [edi+2480]
	shr eax, 7
	mov edx, DWORD PTR [edi+2484]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [edi+2484]
	shr eax, 7
	mov edx, DWORD PTR [edi+2488]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [edi+2488]
	shr eax, 7
	mov edx, DWORD PTR [edi+2492]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [edi+2492]
	shr eax, 7
	mov edx, DWORD PTR [edi+2496]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2492], eax
	mov eax, DWORD PTR [edi+2496]
	shr eax, 7
	mov edx, DWORD PTR [edi+2500]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [edi+2500]
	shr eax, 7
	mov edx, DWORD PTR [edi+2504]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [edi+2504]
	shr eax, 7
	mov edx, DWORD PTR [edi+2508]
	and edx, 127
	ror edx, 7
	or eax, edx
	mov DWORD PTR [edi+2504], eax
	mov eax, DWORD PTR [edi+2508]
	shr eax, 7
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
	mov eax, 185150101
	mov DWORD PTR [edi+2944], eax
	mov eax, -2143473681
	mov DWORD PTR [edi+2948], eax
	mov eax, -1096746914
	mov DWORD PTR [edi+2952], eax
	mov eax, 1793517487
	mov DWORD PTR [edi+2956], eax
	mov eax, 1281081935
	mov DWORD PTR [edi+2960], eax
	mov eax, -1966068273
	mov DWORD PTR [edi+2964], eax
	mov eax, 467241630
	mov DWORD PTR [edi+2968], eax
	mov eax, 950107169
	mov DWORD PTR [edi+2972], eax
	mov eax, -85803555
	mov DWORD PTR [edi+2976], eax
	mov eax, -771676715
	mov DWORD PTR [edi+2980], eax
	mov eax, 1515612558
	mov DWORD PTR [edi+2984], eax
	mov eax, -308998450
	mov DWORD PTR [edi+2988], eax
	mov eax, -1989768032
	mov DWORD PTR [edi+2992], eax
	mov eax, 1710507947
	mov DWORD PTR [edi+2996], eax
	mov eax, 1896990689
	mov DWORD PTR [edi+3000], eax
	mov eax, 794552114
	mov DWORD PTR [edi+3004], eax
	mov eax, 231
	mov DWORD PTR [edi+3008], eax
	mov eax, 0
	mov DWORD PTR [edi+3012], eax
	mov eax, -450695018
	mov DWORD PTR [edi+1072], eax
	mov eax, -677862777
	mov DWORD PTR [edi+1076], eax
	mov eax, 47204435
	mov DWORD PTR [edi+1080], eax
	mov eax, -610669582
	mov DWORD PTR [edi+1084], eax
	mov eax, 1143431134
	mov DWORD PTR [edi+1088], eax
	mov eax, -1573668699
	mov DWORD PTR [edi+1092], eax
	mov eax, 322518606
	mov DWORD PTR [edi+1096], eax
	mov eax, -779986016
	mov DWORD PTR [edi+1100], eax
	mov eax, 1880379059
	mov DWORD PTR [edi+1104], eax
	mov eax, 2138596767
	mov DWORD PTR [edi+1108], eax
	mov eax, -1475231368
	mov DWORD PTR [edi+1112], eax
	mov eax, -650428542
	mov DWORD PTR [edi+1116], eax
	mov eax, -1851035387
	mov DWORD PTR [edi+1120], eax
	mov eax, -2110052856
	mov DWORD PTR [edi+1124], eax
	mov eax, -1891401392
	mov DWORD PTR [edi+1128], eax
	mov eax, 814371556
	mov DWORD PTR [edi+1132], eax
	mov eax, 458
	mov DWORD PTR [edi+1136], eax
	mov eax, 0
	mov DWORD PTR [edi+1140], eax
	mov eax, 1538336744
	mov DWORD PTR [edi+1144], eax
	mov eax, 1259206550
	mov DWORD PTR [edi+1148], eax
	mov eax, 361785784
	mov DWORD PTR [edi+1152], eax
	mov eax, -62382875
	mov DWORD PTR [edi+1156], eax
	mov eax, 31086706
	mov DWORD PTR [edi+1160], eax
	mov eax, -2068888301
	mov DWORD PTR [edi+1164], eax
	mov eax, -1881534188
	mov DWORD PTR [edi+1168], eax
	mov eax, 2005730179
	mov DWORD PTR [edi+1172], eax
	mov eax, -133005798
	mov DWORD PTR [edi+1176], eax
	mov eax, 980896831
	mov DWORD PTR [edi+1180], eax
	mov eax, 111752491
	mov DWORD PTR [edi+1184], eax
	mov eax, -1718683058
	mov DWORD PTR [edi+1188], eax
	mov eax, -17807580
	mov DWORD PTR [edi+1192], eax
	mov eax, -991131659
	mov DWORD PTR [edi+1196], eax
	mov eax, -353202793
	mov DWORD PTR [edi+1200], eax
	mov eax, -526228651
	mov DWORD PTR [edi+1204], eax
	mov eax, 209
	mov DWORD PTR [edi+1208], eax
	mov eax, 0
	mov DWORD PTR [edi+1212], eax
	mov eax, 0
	mov DWORD PTR [edi+1216], eax
	mov eax, 8388608
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
	mov esi, 83
23:
	sub esi, 1
	cmp esi, 82
	je 24f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4102]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4101]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4100]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
	jmp 25f
24:
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
25:
	mov eax, esi
	mov ecx, 9216
	mul ecx
	mov edx, DWORD PTR [edi+60]
	add edx, eax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	mov ecx, 1
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+48]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+480]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+496]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+768]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+784]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+800]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1008]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1152]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1184]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1664]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1728]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1744]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1760]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1776]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1792]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1808]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1920]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1936]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1952]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2048]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2064]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2080]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2096]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2192]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2208]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2224]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2240]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 17
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2304]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2320]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2336]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2352]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2384]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2448]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2464]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2480]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2496]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2512]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2528]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 19
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2592]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2608]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2624]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2640]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2656]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2736]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2752]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2768]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2784]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2816]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 21
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2912]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2928]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2944]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2960]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 22
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3024]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3040]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3056]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3072]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3088]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3104]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3168]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3184]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3200]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3216]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3232]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3248]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 24
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3312]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3328]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3344]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3360]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3376]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3392]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 25
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3456]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3472]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3488]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3504]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3520]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3536]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3600]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3616]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3632]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3648]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3664]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3680]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3744]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3760]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3776]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3792]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3808]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3824]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 28
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3888]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3904]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3920]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3936]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3952]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3968]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 29
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4032]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4048]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4064]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4080]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4096]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4112]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4176]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4192]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4208]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4224]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4240]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4256]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 31
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4320]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4336]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4352]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4368]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4384]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4400]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4464]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4480]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4496]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4512]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4528]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4544]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4608]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4624]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4640]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4656]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4672]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4688]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 34
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4752]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4768]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4784]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4800]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4816]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4832]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4896]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4912]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4928]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4944]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4960]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4976]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5040]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5056]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5072]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5088]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5104]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5120]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 37
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5184]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5200]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5216]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5232]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5248]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5264]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5328]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5344]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5360]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5376]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5392]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5408]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5472]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5488]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5504]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5520]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5536]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5552]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5616]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5632]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5648]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5664]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5680]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5696]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5760]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5776]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5792]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5808]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5824]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5840]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5904]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5920]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5936]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5952]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5968]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5984]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6048]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6064]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6080]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6096]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6112]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6128]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6192]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6208]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6224]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6240]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6256]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6272]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6336]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6352]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6368]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6384]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6400]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6416]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6480]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6496]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6512]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6528]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6544]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6560]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6624]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6640]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6656]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6672]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6688]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6704]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6768]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6784]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6800]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6816]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6832]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6848]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 49
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6912]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6928]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6944]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6960]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6976]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6992]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7056]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7072]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7088]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7104]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7120]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7136]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7200]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7216]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7232]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7248]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7264]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7280]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7344]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7360]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7376]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7392]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7408]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7424]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7488]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7504]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7520]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7536]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7552]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7568]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7632]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7648]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7664]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7680]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7696]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7712]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7776]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7792]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7808]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7824]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7840]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7856]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7920]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7936]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7952]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7968]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7984]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8000]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8064]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8080]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8096]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8112]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8128]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8144]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8208]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8224]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8240]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8256]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8272]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8288]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8352]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8368]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8384]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8400]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8416]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8432]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8496]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8512]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8528]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8544]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8560]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8576]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8640]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8656]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8672]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8688]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8704]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8720]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8784]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8800]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8816]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8832]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8848]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8864]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8928]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8944]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8960]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8976]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8992]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9008]
	pand xmm6, xmm7
	por xmm5, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+9072]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9088]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9104]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9120]
	pand xmm6, xmm7
	por xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9136]
	pand xmm6, xmm7
	por xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9152]
	pand xmm6, xmm7
	por xmm5, xmm6
	movdqu XMMWORD PTR [edi+1504], xmm0
	movdqu XMMWORD PTR [edi+1520], xmm1
	movdqu XMMWORD PTR [edi+1536], xmm2
	movdqu XMMWORD PTR [edi+1552], xmm3
	movdqu XMMWORD PTR [edi+1568], xmm4
	movdqu XMMWORD PTR [edi+1584], xmm5
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov ecx, 1
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+384]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+816]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+960]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+976]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+992]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1536]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1552]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1680]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1696]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1712]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1840]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1968]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1984]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2112]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2128]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2144]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2256]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2272]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2288]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 17
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2432]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2544]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2560]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2576]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 19
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2688]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2704]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2720]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2832]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2848]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2864]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 21
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2976]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2992]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3008]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 22
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3120]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3136]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3152]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3264]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3280]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3296]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 24
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3408]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3424]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3440]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 25
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3552]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3568]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3584]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3696]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3712]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3728]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3840]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3856]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3872]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 28
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3984]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4000]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4016]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 29
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4128]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4144]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4160]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4272]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4288]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4304]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 31
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4416]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4432]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4448]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4560]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4576]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4592]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4704]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4720]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4736]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 34
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4848]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4864]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+4880]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+4992]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5008]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5024]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5136]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5152]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5168]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 37
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5280]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5296]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5312]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5424]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5440]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5456]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5568]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5584]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5600]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5712]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5728]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5744]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+5856]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5872]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+5888]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6000]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6016]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6032]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6144]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6160]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6176]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6288]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6304]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6320]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6432]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6448]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6464]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6576]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6592]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6608]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6720]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6736]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6752]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+6864]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6880]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+6896]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 49
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7008]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7024]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7040]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7152]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7168]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7184]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7296]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7312]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7328]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7440]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7456]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7472]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7584]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7600]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7616]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7728]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7744]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7760]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+7872]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7888]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+7904]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8016]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8032]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8048]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8192]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8304]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8320]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8336]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8448]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8464]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8480]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8592]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8608]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8624]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8736]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8752]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8768]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+8880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+8912]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+9024]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9040]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9056]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+9168]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9184]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+9200]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu XMMWORD PTR [edi+1600], xmm0
	movdqu XMMWORD PTR [edi+1616], xmm1
	movdqu XMMWORD PTR [edi+1632], xmm2
	mov eax, 0
	mov DWORD PTR [edi+1648], eax
	mov eax, 8388608
	mov DWORD PTR [edi+1652], eax
	mov eax, 0
	mov DWORD PTR [edi+1656], eax
	mov eax, 0
	mov DWORD PTR [edi+1660], eax
	mov eax, 0
	mov DWORD PTR [edi+1664], eax
	mov eax, 0
	mov DWORD PTR [edi+1668], eax
	mov eax, 0
	mov DWORD PTR [edi+1672], eax
	mov eax, 0
	mov DWORD PTR [edi+1676], eax
	mov eax, 0
	mov DWORD PTR [edi+1680], eax
	mov eax, 0
	mov DWORD PTR [edi+1684], eax
	mov eax, 0
	mov DWORD PTR [edi+1688], eax
	mov eax, 0
	mov DWORD PTR [edi+1692], eax
	mov eax, 0
	mov DWORD PTR [edi+1696], eax
	mov eax, 0
	mov DWORD PTR [edi+1700], eax
	mov eax, 0
	mov DWORD PTR [edi+1704], eax
	mov eax, 0
	mov DWORD PTR [edi+1708], eax
	mov eax, 0
	mov DWORD PTR [edi+1712], eax
	mov eax, 0
	mov DWORD PTR [edi+1716], eax
	mov ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+1576]
	mov edx, DWORD PTR [edi+1648]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1580]
	mov edx, DWORD PTR [edi+1652]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1584]
	mov edx, DWORD PTR [edi+1656]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1588]
	mov edx, DWORD PTR [edi+1660]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1592]
	mov edx, DWORD PTR [edi+1664]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1596]
	mov edx, DWORD PTR [edi+1668]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+1600]
	mov edx, DWORD PTR [edi+1672]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+1604]
	mov edx, DWORD PTR [edi+1676]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+1608]
	mov edx, DWORD PTR [edi+1680]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+1612]
	mov edx, DWORD PTR [edi+1684]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+1616]
	mov edx, DWORD PTR [edi+1688]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+1620]
	mov edx, DWORD PTR [edi+1692]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+1624]
	mov edx, DWORD PTR [edi+1696]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+1628]
	mov edx, DWORD PTR [edi+1700]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+1632]
	mov edx, DWORD PTR [edi+1704]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+1636]
	mov edx, DWORD PTR [edi+1708]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+1640]
	mov edx, DWORD PTR [edi+1712]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+1644]
	mov edx, DWORD PTR [edi+1716]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1644], eax
	mov eax, DWORD PTR [edi+1648]
	mov edx, DWORD PTR [edi+280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [edi+1652]
	mov edx, DWORD PTR [edi+284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [edi+1656]
	mov edx, DWORD PTR [edi+288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [edi+1660]
	mov edx, DWORD PTR [edi+292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [edi+1664]
	mov edx, DWORD PTR [edi+296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [edi+1668]
	mov edx, DWORD PTR [edi+300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [edi+1672]
	mov edx, DWORD PTR [edi+304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [edi+1676]
	mov edx, DWORD PTR [edi+308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [edi+1680]
	mov edx, DWORD PTR [edi+312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [edi+1684]
	mov edx, DWORD PTR [edi+316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [edi+1688]
	mov edx, DWORD PTR [edi+320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [edi+1692]
	mov edx, DWORD PTR [edi+324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1692], eax
	mov eax, DWORD PTR [edi+1696]
	mov edx, DWORD PTR [edi+328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1696], eax
	mov eax, DWORD PTR [edi+1700]
	mov edx, DWORD PTR [edi+332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1700], eax
	mov eax, DWORD PTR [edi+1704]
	mov edx, DWORD PTR [edi+336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1704], eax
	mov eax, DWORD PTR [edi+1708]
	mov edx, DWORD PTR [edi+340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1708], eax
	mov eax, DWORD PTR [edi+1712]
	mov edx, DWORD PTR [edi+344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1712], eax
	mov eax, DWORD PTR [edi+1716]
	mov edx, DWORD PTR [edi+348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1716], eax
	mov eax, 1576
	mov ecx, 280
	mov edx, 2224
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 82
	je 26f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4102]
	sub eax, 1
	mov ecx, eax
	jmp 27f
26:
	mov ecx, -1
27:
	mov eax, DWORD PTR [edi+1576]
	mov edx, DWORD PTR [edi+2224]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [edi+1580]
	mov edx, DWORD PTR [edi+2228]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [edi+1584]
	mov edx, DWORD PTR [edi+2232]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [edi+1588]
	mov edx, DWORD PTR [edi+2236]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [edi+1592]
	mov edx, DWORD PTR [edi+2240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [edi+1596]
	mov edx, DWORD PTR [edi+2244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1596], eax
	mov eax, DWORD PTR [edi+1600]
	mov edx, DWORD PTR [edi+2248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [edi+1604]
	mov edx, DWORD PTR [edi+2252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [edi+1608]
	mov edx, DWORD PTR [edi+2256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [edi+1612]
	mov edx, DWORD PTR [edi+2260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [edi+1616]
	mov edx, DWORD PTR [edi+2264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [edi+1620]
	mov edx, DWORD PTR [edi+2268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [edi+1624]
	mov edx, DWORD PTR [edi+2272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [edi+1628]
	mov edx, DWORD PTR [edi+2276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [edi+1632]
	mov edx, DWORD PTR [edi+2280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [edi+1636]
	mov edx, DWORD PTR [edi+2284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [edi+1640]
	mov edx, DWORD PTR [edi+2288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [edi+1644]
	mov edx, DWORD PTR [edi+2292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1644], eax
	mov eax, 1504
	mov ecx, 1072
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
	mov eax, 1576
	mov ecx, 1144
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
	mov eax, 1648
	mov ecx, 1216
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
	mov eax, 1144
	mov ecx, 1072
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
	mov eax, 1576
	mov ecx, 1504
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
	mov eax, 1216
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
	mov eax, 1648
	mov ecx, 1504
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
	mov eax, 1216
	mov ecx, 1144
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
	mov eax, 1648
	mov ecx, 1576
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
	mov ecx, 2944
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
	mov ecx, 2944
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
	test esi, esi
	jne 23b
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+2220], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+2292], eax
	mov esi, 1
28:
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
	test esi, esi
	jne 28b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 2
29:
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
	test esi, esi
	jne 29b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 4
210:
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
	test esi, esi
	jne 210b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 8
211:
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
	test esi, esi
	jne 211b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 16
212:
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
	test esi, esi
	jne 212b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 32
213:
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
	test esi, esi
	jne 213b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 64
214:
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
	test esi, esi
	jne 214b
	mov eax, 2224
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
	mov esi, 1
215:
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
	test esi, esi
	jne 215b
	mov eax, 1216
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 129
216:
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
	test esi, esi
	jne 216b
	mov eax, 2224
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
	mov esi, 1
217:
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
	test esi, esi
	jne 217b
	mov eax, 1216
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 259
218:
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
	test esi, esi
	jne 218b
	mov eax, 2224
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
	mov esi, 1
219:
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
	test esi, esi
	jne 219b
	mov eax, 1216
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
	mov esi, 2
220:
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
	test esi, esi
	jne 220b
	mov eax, 1216
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
	mov eax, 280
	mov ecx, 2584
	mov edx, 2656
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 784
	mov ecx, 2296
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
	mov edx, DWORD PTR [edi+2368]
	sub edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+2372]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+2376]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+2380]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+2384]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+2388]
	sbb edx, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+2392]
	sbb edx, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+2396]
	sbb edx, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+2400]
	sbb edx, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+2404]
	sbb edx, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+2408]
	sbb edx, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+2412]
	sbb edx, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+2416]
	sbb edx, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+2420]
	sbb edx, DWORD PTR [edi+188]
	mov edx, DWORD PTR [edi+2424]
	sbb edx, DWORD PTR [edi+192]
	mov edx, DWORD PTR [edi+2428]
	sbb edx, DWORD PTR [edi+196]
	mov edx, DWORD PTR [edi+2432]
	sbb edx, DWORD PTR [edi+200]
	mov edx, DWORD PTR [edi+2436]
	sbb edx, DWORD PTR [edi+204]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+2368]
	or edx, DWORD PTR [edi+2372]
	or edx, DWORD PTR [edi+2376]
	or edx, DWORD PTR [edi+2380]
	or edx, DWORD PTR [edi+2384]
	or edx, DWORD PTR [edi+2388]
	or edx, DWORD PTR [edi+2392]
	or edx, DWORD PTR [edi+2396]
	or edx, DWORD PTR [edi+2400]
	or edx, DWORD PTR [edi+2404]
	or edx, DWORD PTR [edi+2408]
	or edx, DWORD PTR [edi+2412]
	or edx, DWORD PTR [edi+2416]
	or edx, DWORD PTR [edi+2420]
	or edx, DWORD PTR [edi+2424]
	or edx, DWORD PTR [edi+2428]
	or edx, DWORD PTR [edi+2432]
	or edx, DWORD PTR [edi+2436]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
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
	mov edx, DWORD PTR [edi+2656]
	or edx, DWORD PTR [edi+2660]
	or edx, DWORD PTR [edi+2664]
	or edx, DWORD PTR [edi+2668]
	or edx, DWORD PTR [edi+2672]
	or edx, DWORD PTR [edi+2676]
	or edx, DWORD PTR [edi+2680]
	or edx, DWORD PTR [edi+2684]
	or edx, DWORD PTR [edi+2688]
	or edx, DWORD PTR [edi+2692]
	or edx, DWORD PTR [edi+2696]
	or edx, DWORD PTR [edi+2700]
	or edx, DWORD PTR [edi+2704]
	or edx, DWORD PTR [edi+2708]
	or edx, DWORD PTR [edi+2712]
	or edx, DWORD PTR [edi+2716]
	or edx, DWORD PTR [edi+2720]
	or edx, DWORD PTR [edi+2724]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov eax, DWORD PTR [edi+2728]
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+2732]
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+2736]
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+2740]
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+2744]
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+2748]
	mov DWORD PTR [edi+2172], eax
	mov eax, DWORD PTR [edi+2752]
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+2756]
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [edi+2760]
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [edi+2764]
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [edi+2768]
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [edi+2772]
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [edi+2776]
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [edi+2780]
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [edi+2784]
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [edi+2788]
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [edi+2792]
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [edi+2796]
	mov DWORD PTR [edi+2220], eax
	mov eax, DWORD PTR [edi+2728]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2732]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2736]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2740]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2744]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2748]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2752]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2756]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2760]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2764]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2768]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2772]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2776]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2780]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2784]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2788]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2792]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2796]
	mov DWORD PTR [edi+2292], eax
	mov esi, 1
221:
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
	test esi, esi
	jne 221b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 2
222:
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
	test esi, esi
	jne 222b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 4
223:
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
	test esi, esi
	jne 223b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 8
224:
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
	test esi, esi
	jne 224b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 16
225:
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
	test esi, esi
	jne 225b
	mov eax, 2224
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 32
226:
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
	test esi, esi
	jne 226b
	mov eax, 2224
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
	mov esi, 1
227:
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
	test esi, esi
	jne 227b
	mov eax, 2728
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 65
228:
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
	test esi, esi
	jne 228b
	mov eax, 2224
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
	mov esi, 1
229:
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
	test esi, esi
	jne 229b
	mov eax, 2728
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
	mov eax, DWORD PTR [edi+2152]
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [edi+2156]
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [edi+2160]
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [edi+2164]
	mov DWORD PTR [edi+2236], eax
	mov eax, DWORD PTR [edi+2168]
	mov DWORD PTR [edi+2240], eax
	mov eax, DWORD PTR [edi+2172]
	mov DWORD PTR [edi+2244], eax
	mov eax, DWORD PTR [edi+2176]
	mov DWORD PTR [edi+2248], eax
	mov eax, DWORD PTR [edi+2180]
	mov DWORD PTR [edi+2252], eax
	mov eax, DWORD PTR [edi+2184]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [edi+2188]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [edi+2192]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [edi+2196]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [edi+2200]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [edi+2204]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [edi+2208]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [edi+2212]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [edi+2216]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [edi+2220]
	mov DWORD PTR [edi+2292], eax
	mov esi, 131
230:
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
	test esi, esi
	jne 230b
	mov eax, 2224
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
	mov esi, 259
231:
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
	jne 231b
	mov eax, 784
	mov ecx, 2656
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
	mov eax, 784
	mov ecx, 2368
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
	mov eax, 784
	mov ecx, 2440
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
	mov eax, 2872
	mov ecx, 2800
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
	mov eax, 2944
	mov ecx, 3016
	mov edx, 3016
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 3016
	mov ecx, 2152
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
	mov ecx, 3088
	mov edx, 3160
	push eax
	push ecx
	push edx
	push edi
	call {vg_p521_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+3160]
	or edx, DWORD PTR [edi+3164]
	or edx, DWORD PTR [edi+3168]
	or edx, DWORD PTR [edi+3172]
	or edx, DWORD PTR [edi+3176]
	or edx, DWORD PTR [edi+3180]
	or edx, DWORD PTR [edi+3184]
	or edx, DWORD PTR [edi+3188]
	or edx, DWORD PTR [edi+3192]
	or edx, DWORD PTR [edi+3196]
	or edx, DWORD PTR [edi+3200]
	or edx, DWORD PTR [edi+3204]
	or edx, DWORD PTR [edi+3208]
	or edx, DWORD PTR [edi+3212]
	or edx, DWORD PTR [edi+3216]
	or edx, DWORD PTR [edi+3220]
	or edx, DWORD PTR [edi+3224]
	or edx, DWORD PTR [edi+3228]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+3232]
	and eax, edx
	mov DWORD PTR [edi+3232], eax
	mov ecx, DWORD PTR [edi+3232]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+2656]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+62], eax
	mov eax, DWORD PTR [edi+2660]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+58], eax
	mov eax, DWORD PTR [edi+2664]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+54], eax
	mov eax, DWORD PTR [edi+2668]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+50], eax
	mov eax, DWORD PTR [edi+2672]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+46], eax
	mov eax, DWORD PTR [edi+2676]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+42], eax
	mov eax, DWORD PTR [edi+2680]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+38], eax
	mov eax, DWORD PTR [edi+2684]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+34], eax
	mov eax, DWORD PTR [edi+2688]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+30], eax
	mov eax, DWORD PTR [edi+2692]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+26], eax
	mov eax, DWORD PTR [edi+2696]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+22], eax
	mov eax, DWORD PTR [edi+2700]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+18], eax
	mov eax, DWORD PTR [edi+2704]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+14], eax
	mov eax, DWORD PTR [edi+2708]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+10], eax
	mov eax, DWORD PTR [edi+2712]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+6], eax
	mov eax, DWORD PTR [edi+2716]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+2], eax
	mov eax, DWORD PTR [edi+2720]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [ebx], dl
	mov edx, eax
	mov BYTE PTR [ebx+1], dl
	mov eax, DWORD PTR [edi+3160]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+128], eax
	mov eax, DWORD PTR [edi+3164]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+124], eax
	mov eax, DWORD PTR [edi+3168]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+120], eax
	mov eax, DWORD PTR [edi+3172]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+116], eax
	mov eax, DWORD PTR [edi+3176]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+112], eax
	mov eax, DWORD PTR [edi+3180]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+108], eax
	mov eax, DWORD PTR [edi+3184]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+104], eax
	mov eax, DWORD PTR [edi+3188]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+100], eax
	mov eax, DWORD PTR [edi+3192]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+96], eax
	mov eax, DWORD PTR [edi+3196]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+92], eax
	mov eax, DWORD PTR [edi+3200]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+88], eax
	mov eax, DWORD PTR [edi+3204]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+84], eax
	mov eax, DWORD PTR [edi+3208]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+80], eax
	mov eax, DWORD PTR [edi+3212]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+76], eax
	mov eax, DWORD PTR [edi+3216]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+72], eax
	mov eax, DWORD PTR [edi+3220]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+68], eax
	mov eax, DWORD PTR [edi+3224]
	and eax, ecx
	mov edx, eax
	shr edx, 8
	mov BYTE PTR [ebx+66], dl
	mov edx, eax
	mov BYTE PTR [ebx+67], dl
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
