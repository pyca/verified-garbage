// The functions of `src/ecdsa_p521.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_sign:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+58]
	bswap rax
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rcx+50]
	bswap rax
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rcx+42]
	bswap rax
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rcx+34]
	bswap rax
	mov QWORD PTR [rdi+2320], rax
	mov rax, QWORD PTR [rcx+26]
	bswap rax
	mov QWORD PTR [rdi+2328], rax
	mov rax, QWORD PTR [rcx+18]
	bswap rax
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rcx+10]
	bswap rax
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rcx+2]
	bswap rax
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2360], rax
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2504], rax
	mov rax, QWORD PTR [rdi+2440]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2448]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdi+2448]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2456]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdi+2456]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2464]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdi+2464]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2472]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdi+2472]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2480]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdi+2480]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2488]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdi+2488]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2496]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdi+2496]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2504]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdi+2504]
	shr rax, 7
	mov QWORD PTR [rdi+2504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -1
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -1
	mov QWORD PTR [rdi+120], rax
	movabs rax, 511
	mov QWORD PTR [rdi+128], rax
	movabs rax, -4940528924288850935
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+144], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+152], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+160], rax
	movabs rax, -6
	mov QWORD PTR [rdi+168], rax
	movabs rax, -1
	mov QWORD PTR [rdi+176], rax
	movabs rax, -1
	mov QWORD PTR [rdi+184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 511
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 1
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+416], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+488], rax
	movabs rax, -108086391056891905
	mov QWORD PTR [rdi+496], rax
	movabs rax, -1
	mov QWORD PTR [rdi+504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+512], rax
	movabs rax, -1
	mov QWORD PTR [rdi+520], rax
	movabs rax, -1
	mov QWORD PTR [rdi+528], rax
	movabs rax, -1
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 511
	mov QWORD PTR [rdi+560], rax
	movabs rax, -9206149359546586475
	mov QWORD PTR [rdi+568], rax
	movabs rax, 7703098954667325534
	mov QWORD PTR [rdi+576], rax
	movabs rax, -8444198932957117873
	mov QWORD PTR [rdi+584], rax
	movabs rax, 4080679219017386654
	mov QWORD PTR [rdi+592], rax
	movabs rax, -3314326249800548899
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1327138235749078642
	mov QWORD PTR [rdi+608], rax
	movabs rax, 7346575694218300576
	mov QWORD PTR [rdi+616], rax
	movabs rax, 3412575346494654433
	mov QWORD PTR [rdi+624], rax
	movabs rax, 231
	mov QWORD PTR [rdi+632], rax
	movabs rax, -5534465018312146687
	mov QWORD PTR [rdi+640], rax
	movabs rax, 5619576712772809438
	mov QWORD PTR [rdi+648], rax
	movabs rax, 8005610518557668641
	mov QWORD PTR [rdi+656], rax
	movabs rax, -7746456476338520108
	mov QWORD PTR [rdi+664], rax
	movabs rax, -2499315621146659924
	mov QWORD PTR [rdi+672], rax
	movabs rax, -7999496471265827170
	mov QWORD PTR [rdi+680], rax
	movabs rax, 2399910904520155098
	mov QWORD PTR [rdi+688], rax
	movabs rax, -1815197603150574886
	mov QWORD PTR [rdi+696], rax
	movabs rax, 116
	mov QWORD PTR [rdi+704], rax
	movabs rax, 2902022722397546126
	mov QWORD PTR [rdi+712], rax
	movabs rax, 2325088080057329843
	mov QWORD PTR [rdi+720], rax
	movabs rax, -5721086412136040095
	mov QWORD PTR [rdi+728], rax
	movabs rax, 2333612672179754627
	mov QWORD PTR [rdi+736], rax
	movabs rax, 1606649517559478803
	mov QWORD PTR [rdi+744], rax
	movabs rax, 3750328465540489011
	mov QWORD PTR [rdi+752], rax
	movabs rax, -1383596148691055198
	mov QWORD PTR [rdi+760], rax
	movabs rax, 157139108829216397
	mov QWORD PTR [rdi+768], rax
	movabs rax, 480
	mov QWORD PTR [rdi+776], rax
	movabs rax, 1404226216438127876
	mov QWORD PTR [rdi+784], rax
	movabs rax, -646342563601285469
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1344198287485662207
	mov QWORD PTR [rdi+800], rax
	movabs rax, -3210469545270092282
	mov QWORD PTR [rdi+808], rax
	movabs rax, -2491014132492810277
	mov QWORD PTR [rdi+816], rax
	movabs rax, -3462193604041806274
	mov QWORD PTR [rdi+824], rax
	movabs rax, 6614782218913277884
	mov QWORD PTR [rdi+832], rax
	movabs rax, 3282565375810407749
	mov QWORD PTR [rdi+840], rax
	movabs rax, 61
	mov QWORD PTR [rdi+848], rax
	movabs rax, -324259173170675712
	mov QWORD PTR [rdi+856], rax
	movabs rax, 2927982029091333069
	mov QWORD PTR [rdi+864], rax
	movabs rax, 1720978806102766044
	mov QWORD PTR [rdi+872], rax
	movabs rax, -3873067094995862739
	mov QWORD PTR [rdi+880], rax
	movabs rax, 204699087262476340
	mov QWORD PTR [rdi+888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+920], rax
	movabs rax, -3
	mov QWORD PTR [rdi+928], rax
	movabs rax, -1
	mov QWORD PTR [rdi+936], rax
	movabs rax, -1
	mov QWORD PTR [rdi+944], rax
	movabs rax, -1
	mov QWORD PTR [rdi+952], rax
	movabs rax, -1
	mov QWORD PTR [rdi+960], rax
	movabs rax, -1
	mov QWORD PTR [rdi+968], rax
	movabs rax, -1
	mov QWORD PTR [rdi+976], rax
	movabs rax, -1
	mov QWORD PTR [rdi+984], rax
	movabs rax, 511
	mov QWORD PTR [rdi+992], rax
	movabs rax, -4940528924288850937
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -6
	mov QWORD PTR [rdi+1032], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 511
	mov QWORD PTR [rdi+1064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	movabs rax, -1
	mov QWORD PTR [rdi+3232], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3888], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3889], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3890], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3891], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3892], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3893], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3894], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3895], dl
	add rbx, 1
	cmp rbx, 72
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+1000]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4472], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4473], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4474], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4475], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4476], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4477], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4478], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4479], dl
	add rbx, 1
	cmp rbx, 72
	jne 22b
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	movabs rax, -2911398454546468714
	mov QWORD PTR [rdi+1072], rax
	movabs rax, -2622805883304785837
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -6758855595800436770
	mov QWORD PTR [rdi+1088], rax
	movabs rax, -3350014429734814130
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 9185203175476711091
	mov QWORD PTR [rdi+1104], rax
	movabs rax, -2793569313455226504
	mov QWORD PTR [rdi+1112], rax
	movabs rax, -9062608006907465467
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 3497699202216198480
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 458
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 5408250952697325544
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -267932407593670216
	mov QWORD PTR [rdi+1152], rax
	movabs rax, -8885807591840917390
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 8614545525818659092
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 4212919814057000474
	mov QWORD PTR [rdi+1176], rax
	movabs rax, -7381687526187518677
	mov QWORD PTR [rdi+1184], rax
	movabs rax, -4256878057158064348
	mov QWORD PTR [rdi+1192], rax
	movabs rax, -2260134842321433193
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 209
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov eax, 0
	mov QWORD PTR [rdi+3880], rax
	mov ebx, 83
23:
	sub rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 9216
	mul rcx
	lea rdx, {VG_P521_COMB}
	add rdx, rax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	pxor xmm8, xmm8
	mov ecx, 1
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+16]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+32]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+48]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+64]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+80]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+96]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+112]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+128]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 2
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+144]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+160]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+176]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+192]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+208]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+224]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+240]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+256]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+272]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 3
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+288]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+304]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+320]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+336]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+352]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+368]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+384]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+400]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+416]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 4
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+432]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+448]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+464]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+480]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+496]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+512]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+528]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+544]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+560]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 5
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+576]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+592]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+608]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+624]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+640]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+656]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+672]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+688]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+704]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 6
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+720]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+736]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+752]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+768]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+784]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+800]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+816]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+832]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+848]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 7
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+864]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+880]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+896]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+912]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+928]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+944]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+960]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+976]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+992]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 8
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1008]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1024]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1040]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1056]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1072]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1088]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1104]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1120]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1136]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 9
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1152]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1168]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1184]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1200]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1216]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1232]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1248]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1264]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1280]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 10
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1296]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1312]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1328]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1344]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1360]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1376]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1392]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1408]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1424]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 11
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1440]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1456]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1472]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1488]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1504]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1520]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1536]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1552]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1568]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 12
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1584]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1600]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1616]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1632]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1648]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1664]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1680]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1696]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1712]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 13
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1728]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1744]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1760]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1776]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1792]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1808]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1824]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1840]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1856]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 14
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+1872]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1888]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1904]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1920]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1936]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1952]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1968]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+1984]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2000]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 15
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2016]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2032]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2048]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2064]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2080]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2096]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2112]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2128]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2144]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 16
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2160]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2176]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2192]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2208]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2224]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2240]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2256]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2272]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2288]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 17
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2304]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2320]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2336]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2352]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2368]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2384]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2400]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2416]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2432]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 18
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2448]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2464]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2480]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2496]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2512]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2528]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2544]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2560]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2576]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 19
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2592]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2608]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2624]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2640]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2656]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2672]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2688]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2704]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2720]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 20
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2736]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2752]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2768]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2784]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2800]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2816]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2832]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2848]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2864]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 21
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+2880]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2896]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2912]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2928]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2944]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2960]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2976]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+2992]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3008]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 22
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3024]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3040]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3056]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3072]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3088]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3104]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3120]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3136]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3152]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 23
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3168]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3184]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3200]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3216]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3232]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3248]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3264]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3280]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3296]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 24
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3312]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3328]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3344]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3360]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3376]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3392]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3408]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3424]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3440]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 25
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3456]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3472]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3488]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3504]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3520]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3536]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3552]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3568]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3584]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 26
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3600]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3616]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3632]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3648]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3664]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3680]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3696]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3712]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3728]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 27
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3744]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3760]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3776]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3792]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3808]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3824]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3840]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3856]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3872]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 28
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+3888]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3904]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3920]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3936]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3952]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3968]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+3984]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4000]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4016]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 29
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4032]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4048]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4064]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4080]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4096]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4112]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4128]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4144]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4160]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 30
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4176]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4192]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4208]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4224]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4240]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4256]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4272]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4288]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4304]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 31
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4320]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4336]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4352]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4368]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4384]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4400]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4416]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4432]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4448]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 32
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4464]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4480]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4496]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4512]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4528]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4544]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4560]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4576]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4592]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 33
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4608]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4624]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4640]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4656]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4672]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4688]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4704]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4720]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4736]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 34
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4752]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4768]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4784]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4800]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4816]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4832]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4848]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4864]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4880]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 35
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+4896]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4912]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4928]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4944]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4960]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4976]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+4992]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5008]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5024]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 36
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5040]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5056]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5072]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5088]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5104]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5120]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5136]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5152]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5168]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 37
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5184]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5200]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5216]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5232]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5248]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5264]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5280]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5296]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5312]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 38
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5328]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5344]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5360]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5376]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5392]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5408]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5424]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5440]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5456]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 39
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5472]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5488]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5504]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5520]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5536]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5552]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5568]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5584]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5600]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 40
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5616]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5632]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5648]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5664]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5680]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5696]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5712]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5728]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5744]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 41
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5760]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5776]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5792]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5808]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5824]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5840]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5856]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5872]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5888]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 42
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+5904]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5920]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5936]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5952]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5968]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+5984]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6000]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6016]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6032]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 43
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6048]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6064]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6080]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6096]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6112]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6128]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6144]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6160]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6176]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 44
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6192]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6208]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6224]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6240]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6256]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6272]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6288]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6304]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6320]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 45
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6336]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6352]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6368]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6384]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6400]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6416]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6432]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6448]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6464]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 46
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6480]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6496]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6512]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6528]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6544]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6560]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6576]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6592]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6608]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 47
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6624]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6640]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6656]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6672]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6688]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6704]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6720]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6736]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6752]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 48
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6768]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6784]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6800]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6816]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6832]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6848]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6864]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6880]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6896]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 49
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+6912]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6928]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6944]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6960]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6976]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+6992]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7008]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7024]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7040]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 50
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7056]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7072]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7088]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7104]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7120]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7136]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7152]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7168]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7184]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 51
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7200]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7216]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7232]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7248]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7264]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7280]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7296]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7312]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7328]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 52
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7344]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7360]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7376]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7392]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7408]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7424]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7440]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7456]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7472]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 53
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7488]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7504]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7520]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7536]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7552]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7568]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7584]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7600]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7616]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 54
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7632]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7648]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7664]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7680]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7696]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7712]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7728]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7744]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7760]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 55
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7776]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7792]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7808]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7824]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7840]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7856]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7872]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7888]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7904]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 56
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+7920]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7936]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7952]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7968]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+7984]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8000]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8016]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8032]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8048]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 57
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8064]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8080]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8096]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8112]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8128]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8144]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8160]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8176]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8192]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 58
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8208]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8224]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8240]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8256]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8272]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8288]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8304]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8320]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8336]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 59
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8352]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8368]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8384]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8400]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8416]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8432]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8448]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8464]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8480]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 60
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8496]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8512]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8528]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8544]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8560]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8576]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8592]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8608]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8624]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 61
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8640]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8656]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8672]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8688]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8704]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8720]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8736]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8752]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8768]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 62
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8784]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8800]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8816]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8832]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8848]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8864]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8880]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8896]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8912]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 63
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+8928]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8944]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8960]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8976]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+8992]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9008]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9024]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9040]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9056]
	pand xmm14, xmm15
	por xmm8, xmm14
	mov ecx, 64
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movq xmm15, rcx
	punpcklqdq xmm15, xmm15
	movdqu xmm14, XMMWORD PTR [rdx+9072]
	pand xmm14, xmm15
	por xmm0, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9088]
	pand xmm14, xmm15
	por xmm1, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9104]
	pand xmm14, xmm15
	por xmm2, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9120]
	pand xmm14, xmm15
	por xmm3, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9136]
	pand xmm14, xmm15
	por xmm4, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9152]
	pand xmm14, xmm15
	por xmm5, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9168]
	pand xmm14, xmm15
	por xmm6, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9184]
	pand xmm14, xmm15
	por xmm7, xmm14
	movdqu xmm14, XMMWORD PTR [rdx+9200]
	pand xmm14, xmm15
	por xmm8, xmm14
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu XMMWORD PTR [rdi+1632], xmm8
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	xor rcx, -1
	movabs rax, 36028797018963968
	and rax, rcx
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1712], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+3310]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1072
	mov ecx, 1504
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1576
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 2008
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1360
	mov edx, 1504
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -288
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 576
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov ecx, 0
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1152]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1160]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1168]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1176]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1184]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1192]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1200]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1208]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1280], rax
	test rbx, rbx
	jne 23b
	call {vg_p521_inv_mod_p}
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2152]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2160]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2168]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2176]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2184]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2192]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2200]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2208]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2216]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2512], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2520], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2528], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2536], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2544], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2552], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2560], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2568], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2576], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2512]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2512], rdx
	mov rdx, QWORD PTR [rdi+2520]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2520], rdx
	mov rdx, QWORD PTR [rdi+2528]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2528], rdx
	mov rdx, QWORD PTR [rdi+2536]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2536], rdx
	mov rdx, QWORD PTR [rdi+2544]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2544], rdx
	mov rdx, QWORD PTR [rdi+2552]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2552], rdx
	mov rdx, QWORD PTR [rdi+2560]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2560], rdx
	mov rdx, QWORD PTR [rdi+2568]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2568], rdx
	mov rdx, QWORD PTR [rdi+2576]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2576], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2512]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+352]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2520]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+360]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2528]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+368]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2536]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+376]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2544]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+384]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2552]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+392]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2560]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+400]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2568]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+408]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+416]
	mov rax, QWORD PTR [rdi+2576]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2584], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2592], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2600], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2608], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2616], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2624], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2632], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2640], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2648], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2584]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2584], rdx
	mov rdx, QWORD PTR [rdi+2592]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2592], rdx
	mov rdx, QWORD PTR [rdi+2600]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2600], rdx
	mov rdx, QWORD PTR [rdi+2608]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2608], rdx
	mov rdx, QWORD PTR [rdi+2616]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2616], rdx
	mov rdx, QWORD PTR [rdi+2624]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2624], rdx
	mov rdx, QWORD PTR [rdi+2632]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2632], rdx
	mov rdx, QWORD PTR [rdi+2640]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2640], rdx
	mov rdx, QWORD PTR [rdi+2648]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2648], rdx
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2584]
	add r8, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+4024], r8
	mov r8, QWORD PTR [rdi+2592]
	adc r8, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+2600]
	adc r8, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+2608]
	adc r8, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+2616]
	adc r8, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+2624]
	adc r8, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+2632]
	adc r8, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+2640]
	adc r8, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+2648]
	adc r8, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2656], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2664], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2672], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2680], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2688], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2696], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2704], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+2712], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+2720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2656]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2656], rdx
	mov rdx, QWORD PTR [rdi+2664]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2664], rdx
	mov rdx, QWORD PTR [rdi+2672]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2672], rdx
	mov rdx, QWORD PTR [rdi+2680]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2680], rdx
	mov rdx, QWORD PTR [rdi+2688]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2688], rdx
	mov rdx, QWORD PTR [rdi+2696]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2696], rdx
	mov rdx, QWORD PTR [rdi+2704]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2704], rdx
	mov rdx, QWORD PTR [rdi+2712]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2712], rdx
	mov rdx, QWORD PTR [rdi+2720]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2720], rdx
	mov r12, rsi
	mov esi, 2728
	mov edx, 2296
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+2368]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2376]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2384]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2392]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2400]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2408]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2416]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2424]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2432]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2368]
	or rdx, QWORD PTR [rdi+2376]
	or rdx, QWORD PTR [rdi+2384]
	or rdx, QWORD PTR [rdi+2392]
	or rdx, QWORD PTR [rdi+2400]
	or rdx, QWORD PTR [rdi+2408]
	or rdx, QWORD PTR [rdi+2416]
	or rdx, QWORD PTR [rdi+2424]
	or rdx, QWORD PTR [rdi+2432]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2296]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2304]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2312]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2320]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2328]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2336]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2344]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2352]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2360]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2296]
	or rdx, QWORD PTR [rdi+2304]
	or rdx, QWORD PTR [rdi+2312]
	or rdx, QWORD PTR [rdi+2320]
	or rdx, QWORD PTR [rdi+2328]
	or rdx, QWORD PTR [rdi+2336]
	or rdx, QWORD PTR [rdi+2344]
	or rdx, QWORD PTR [rdi+2352]
	or rdx, QWORD PTR [rdi+2360]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2656]
	or rdx, QWORD PTR [rdi+2664]
	or rdx, QWORD PTR [rdi+2672]
	or rdx, QWORD PTR [rdi+2680]
	or rdx, QWORD PTR [rdi+2688]
	or rdx, QWORD PTR [rdi+2696]
	or rdx, QWORD PTR [rdi+2704]
	or rdx, QWORD PTR [rdi+2712]
	or rdx, QWORD PTR [rdi+2720]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	call {vg_p521_inv_mod_n}
	mov r12, rsi
	mov esi, 2800
	mov edx, 2656
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2872
	mov edx, 2368
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2944
	mov edx, 2440
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2800
	mov ecx, 2872
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+3016]
	add r8, QWORD PTR [rdi+2944]
	mov QWORD PTR [rdi+4024], r8
	mov r8, QWORD PTR [rdi+3024]
	adc r8, QWORD PTR [rdi+2952]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+3032]
	adc r8, QWORD PTR [rdi+2960]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+3040]
	adc r8, QWORD PTR [rdi+2968]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+3048]
	adc r8, QWORD PTR [rdi+2976]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+3056]
	adc r8, QWORD PTR [rdi+2984]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+3064]
	adc r8, QWORD PTR [rdi+2992]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+3072]
	adc r8, QWORD PTR [rdi+3000]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+3080]
	adc r8, QWORD PTR [rdi+3008]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3016], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3024], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3032], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3040], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3048], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3056], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3064], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3072], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3080], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+3016]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3016], rdx
	mov rdx, QWORD PTR [rdi+3024]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3024], rdx
	mov rdx, QWORD PTR [rdi+3032]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3032], rdx
	mov rdx, QWORD PTR [rdi+3040]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3040], rdx
	mov rdx, QWORD PTR [rdi+3048]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3048], rdx
	mov rdx, QWORD PTR [rdi+3056]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3056], rdx
	mov rdx, QWORD PTR [rdi+3064]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3064], rdx
	mov rdx, QWORD PTR [rdi+3072]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3072], rdx
	mov rdx, QWORD PTR [rdi+3080]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3080], rdx
	mov r12, rsi
	mov esi, 3088
	mov edx, 2152
	mov ecx, 3016
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3160
	mov edx, 3088
	mov ecx, 352
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+3160]
	or rdx, QWORD PTR [rdi+3168]
	or rdx, QWORD PTR [rdi+3176]
	or rdx, QWORD PTR [rdi+3184]
	or rdx, QWORD PTR [rdi+3192]
	or rdx, QWORD PTR [rdi+3200]
	or rdx, QWORD PTR [rdi+3208]
	or rdx, QWORD PTR [rdi+3216]
	or rdx, QWORD PTR [rdi+3224]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov rax, QWORD PTR [rdi+2656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+58], rax
	mov rax, QWORD PTR [rdi+2664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+50], rax
	mov rax, QWORD PTR [rdi+2672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+42], rax
	mov rax, QWORD PTR [rdi+2680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+34], rax
	mov rax, QWORD PTR [rdi+2688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+26], rax
	mov rax, QWORD PTR [rdi+2696]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+18], rax
	mov rax, QWORD PTR [rdi+2704]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+10], rax
	mov rax, QWORD PTR [rdi+2712]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+2], rax
	mov rax, QWORD PTR [rdi+2720]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi], dl
	mov rdx, rax
	mov BYTE PTR [rsi+1], dl
	mov rax, QWORD PTR [rdi+3160]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+124], rax
	mov rax, QWORD PTR [rdi+3168]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+116], rax
	mov rax, QWORD PTR [rdi+3176]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+108], rax
	mov rax, QWORD PTR [rdi+3184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+100], rax
	mov rax, QWORD PTR [rdi+3192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+92], rax
	mov rax, QWORD PTR [rdi+3200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+84], rax
	mov rax, QWORD PTR [rdi+3208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+76], rax
	mov rax, QWORD PTR [rdi+3216]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+68], rax
	mov rax, QWORD PTR [rdi+3224]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+66], dl
	mov rdx, rax
	mov BYTE PTR [rsi+67], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ecdsa_p521_verify:
	mov r8, rcx
	mov r9, rdi
	mov rcx, rdx
	mov r10, rdx
	add r10, 66
	mov rdx, rdi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+58]
	bswap rax
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rcx+50]
	bswap rax
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rcx+42]
	bswap rax
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rcx+34]
	bswap rax
	mov QWORD PTR [rdi+2320], rax
	mov rax, QWORD PTR [rcx+26]
	bswap rax
	mov QWORD PTR [rdi+2328], rax
	mov rax, QWORD PTR [rcx+18]
	bswap rax
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rcx+10]
	bswap rax
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rcx+2]
	bswap rax
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2360], rax
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2504], rax
	mov rax, QWORD PTR [rdi+2368]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2376]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rdi+2376]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2384]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rdi+2384]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2392]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rdi+2392]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2400]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rdi+2400]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2408]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rdi+2408]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2416]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rdi+2416]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2424]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rdi+2424]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2432]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rdi+2432]
	shr rax, 7
	mov QWORD PTR [rdi+2432], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -1
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -1
	mov QWORD PTR [rdi+120], rax
	movabs rax, 511
	mov QWORD PTR [rdi+128], rax
	movabs rax, -4940528924288850935
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+144], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+152], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+160], rax
	movabs rax, -6
	mov QWORD PTR [rdi+168], rax
	movabs rax, -1
	mov QWORD PTR [rdi+176], rax
	movabs rax, -1
	mov QWORD PTR [rdi+184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 511
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 1
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+416], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+488], rax
	movabs rax, -108086391056891905
	mov QWORD PTR [rdi+496], rax
	movabs rax, -1
	mov QWORD PTR [rdi+504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+512], rax
	movabs rax, -1
	mov QWORD PTR [rdi+520], rax
	movabs rax, -1
	mov QWORD PTR [rdi+528], rax
	movabs rax, -1
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 511
	mov QWORD PTR [rdi+560], rax
	movabs rax, -9206149359546586475
	mov QWORD PTR [rdi+568], rax
	movabs rax, 7703098954667325534
	mov QWORD PTR [rdi+576], rax
	movabs rax, -8444198932957117873
	mov QWORD PTR [rdi+584], rax
	movabs rax, 4080679219017386654
	mov QWORD PTR [rdi+592], rax
	movabs rax, -3314326249800548899
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1327138235749078642
	mov QWORD PTR [rdi+608], rax
	movabs rax, 7346575694218300576
	mov QWORD PTR [rdi+616], rax
	movabs rax, 3412575346494654433
	mov QWORD PTR [rdi+624], rax
	movabs rax, 231
	mov QWORD PTR [rdi+632], rax
	movabs rax, -5534465018312146687
	mov QWORD PTR [rdi+640], rax
	movabs rax, 5619576712772809438
	mov QWORD PTR [rdi+648], rax
	movabs rax, 8005610518557668641
	mov QWORD PTR [rdi+656], rax
	movabs rax, -7746456476338520108
	mov QWORD PTR [rdi+664], rax
	movabs rax, -2499315621146659924
	mov QWORD PTR [rdi+672], rax
	movabs rax, -7999496471265827170
	mov QWORD PTR [rdi+680], rax
	movabs rax, 2399910904520155098
	mov QWORD PTR [rdi+688], rax
	movabs rax, -1815197603150574886
	mov QWORD PTR [rdi+696], rax
	movabs rax, 116
	mov QWORD PTR [rdi+704], rax
	movabs rax, 2902022722397546126
	mov QWORD PTR [rdi+712], rax
	movabs rax, 2325088080057329843
	mov QWORD PTR [rdi+720], rax
	movabs rax, -5721086412136040095
	mov QWORD PTR [rdi+728], rax
	movabs rax, 2333612672179754627
	mov QWORD PTR [rdi+736], rax
	movabs rax, 1606649517559478803
	mov QWORD PTR [rdi+744], rax
	movabs rax, 3750328465540489011
	mov QWORD PTR [rdi+752], rax
	movabs rax, -1383596148691055198
	mov QWORD PTR [rdi+760], rax
	movabs rax, 157139108829216397
	mov QWORD PTR [rdi+768], rax
	movabs rax, 480
	mov QWORD PTR [rdi+776], rax
	movabs rax, 1404226216438127876
	mov QWORD PTR [rdi+784], rax
	movabs rax, -646342563601285469
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1344198287485662207
	mov QWORD PTR [rdi+800], rax
	movabs rax, -3210469545270092282
	mov QWORD PTR [rdi+808], rax
	movabs rax, -2491014132492810277
	mov QWORD PTR [rdi+816], rax
	movabs rax, -3462193604041806274
	mov QWORD PTR [rdi+824], rax
	movabs rax, 6614782218913277884
	mov QWORD PTR [rdi+832], rax
	movabs rax, 3282565375810407749
	mov QWORD PTR [rdi+840], rax
	movabs rax, 61
	mov QWORD PTR [rdi+848], rax
	movabs rax, -324259173170675712
	mov QWORD PTR [rdi+856], rax
	movabs rax, 2927982029091333069
	mov QWORD PTR [rdi+864], rax
	movabs rax, 1720978806102766044
	mov QWORD PTR [rdi+872], rax
	movabs rax, -3873067094995862739
	mov QWORD PTR [rdi+880], rax
	movabs rax, 204699087262476340
	mov QWORD PTR [rdi+888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+920], rax
	movabs rax, -3
	mov QWORD PTR [rdi+928], rax
	movabs rax, -1
	mov QWORD PTR [rdi+936], rax
	movabs rax, -1
	mov QWORD PTR [rdi+944], rax
	movabs rax, -1
	mov QWORD PTR [rdi+952], rax
	movabs rax, -1
	mov QWORD PTR [rdi+960], rax
	movabs rax, -1
	mov QWORD PTR [rdi+968], rax
	movabs rax, -1
	mov QWORD PTR [rdi+976], rax
	movabs rax, -1
	mov QWORD PTR [rdi+984], rax
	movabs rax, 511
	mov QWORD PTR [rdi+992], rax
	movabs rax, -4940528924288850937
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -6
	mov QWORD PTR [rdi+1032], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 511
	mov QWORD PTR [rdi+1064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	movabs rax, -1
	mov QWORD PTR [rdi+3232], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3888], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3889], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3890], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3891], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3892], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3893], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3894], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3895], dl
	add rbx, 1
	cmp rbx, 72
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+1000]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4472], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4473], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4474], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4475], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4476], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4477], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4478], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4479], dl
	add rbx, 1
	cmp rbx, 72
	jne 22b
	mov rax, QWORD PTR [r10+58]
	bswap rax
	mov QWORD PTR [rdi+2224], rax
	mov rax, QWORD PTR [r10+50]
	bswap rax
	mov QWORD PTR [rdi+2232], rax
	mov rax, QWORD PTR [r10+42]
	bswap rax
	mov QWORD PTR [rdi+2240], rax
	mov rax, QWORD PTR [r10+34]
	bswap rax
	mov QWORD PTR [rdi+2248], rax
	mov rax, QWORD PTR [r10+26]
	bswap rax
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [r10+18]
	bswap rax
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [r10+10]
	bswap rax
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [r10+2]
	bswap rax
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [r10]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2872], rax
	movabs rax, 70368744177664
	mov QWORD PTR [rdi+2880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2936], rax
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	mov rdx, r9
	add rdx, 67
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2656], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2664], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2672], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2680], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2688], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2696], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2704], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2712], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2720], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	call {vg_p521_check_point}
	mov rdx, QWORD PTR [rdi+2296]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2304]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2312]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2320]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2328]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2336]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2344]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2352]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2360]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2296]
	or rdx, QWORD PTR [rdi+2304]
	or rdx, QWORD PTR [rdi+2312]
	or rdx, QWORD PTR [rdi+2320]
	or rdx, QWORD PTR [rdi+2328]
	or rdx, QWORD PTR [rdi+2336]
	or rdx, QWORD PTR [rdi+2344]
	or rdx, QWORD PTR [rdi+2352]
	or rdx, QWORD PTR [rdi+2360]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2224]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2232]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2240]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2248]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2256]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2264]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2272]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2280]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2288]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2224]
	or rdx, QWORD PTR [rdi+2232]
	or rdx, QWORD PTR [rdi+2240]
	or rdx, QWORD PTR [rdi+2248]
	or rdx, QWORD PTR [rdi+2256]
	or rdx, QWORD PTR [rdi+2264]
	or rdx, QWORD PTR [rdi+2272]
	or rdx, QWORD PTR [rdi+2280]
	or rdx, QWORD PTR [rdi+2288]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov r12, rsi
	mov esi, 2728
	mov edx, 2224
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	call {vg_p521_inv_mod_n}
	mov r12, rsi
	mov esi, 2944
	mov edx, 2368
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2872
	mov edx, 2296
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2944
	mov ecx, 2152
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3088
	mov edx, 2872
	mov ecx, 2152
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2512
	mov edx, 3016
	mov ecx, 352
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2584
	mov edx, 3088
	mov ecx, 352
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+2512]
	mov r9, QWORD PTR [rdi+2520]
	mov r10, QWORD PTR [rdi+2528]
	mov r11, QWORD PTR [rdi+2536]
	mov r12, QWORD PTR [rdi+2544]
	mov r13, QWORD PTR [rdi+2552]
	mov r14, QWORD PTR [rdi+2560]
	mov r15, QWORD PTR [rdi+2568]
	mov rbp, QWORD PTR [rdi+2576]
	mov esi, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+3304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3880], rax
23:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 24f
	mov rcx, r8
	and rcx, 127
	cmp rcx, 64
	jb 26f
	sub rcx, 128
	jmp 27f
26:
27:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	sbb r15, rdx
	sbb rbp, rdx
	sbb rsi, rdx
	mov BYTE PTR [rdi+rbx*1+3304], cl
	shr r8, 7
	mov rax, r9
	shl rax, 57
	or r8, rax
	shr r9, 7
	mov rax, r10
	shl rax, 57
	or r9, rax
	shr r10, 7
	mov rax, r11
	shl rax, 57
	or r10, rax
	shr r11, 7
	mov rax, r12
	shl rax, 57
	or r11, rax
	shr r12, 7
	mov rax, r13
	shl rax, 57
	or r12, rax
	shr r13, 7
	mov rax, r14
	shl rax, 57
	or r13, rax
	shr r14, 7
	mov rax, r15
	shl rax, 57
	or r14, rax
	shr r15, 7
	mov rax, rbp
	shl rax, 57
	or r15, rax
	shr rbp, 7
	mov rax, rsi
	shl rax, 57
	or rbp, rax
	shr rsi, 7
	add rbx, 7
	jmp 25f
24:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	mov rax, r15
	shl rax, 63
	or r14, rax
	shr r15, 1
	mov rax, rbp
	shl rax, 63
	or r15, rax
	shr rbp, 1
	mov rax, rsi
	shl rax, 63
	or rbp, rax
	shr rsi, 1
	add rbx, 1
25:
	cmp rbx, 577
	jb 23b
	mov r8, QWORD PTR [rdi+2584]
	mov r9, QWORD PTR [rdi+2592]
	mov r10, QWORD PTR [rdi+2600]
	mov r11, QWORD PTR [rdi+2608]
	mov r12, QWORD PTR [rdi+2616]
	mov r13, QWORD PTR [rdi+2624]
	mov r14, QWORD PTR [rdi+2632]
	mov r15, QWORD PTR [rdi+2640]
	mov rbp, QWORD PTR [rdi+2648]
	mov esi, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+5320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5896], rax
28:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 29f
	mov rcx, r8
	and rcx, 31
	cmp rcx, 16
	jb 211f
	sub rcx, 32
	jmp 212f
211:
212:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	sbb r15, rdx
	sbb rbp, rdx
	sbb rsi, rdx
	mov BYTE PTR [rdi+rbx*1+5320], cl
	shr r8, 5
	mov rax, r9
	shl rax, 59
	or r8, rax
	shr r9, 5
	mov rax, r10
	shl rax, 59
	or r9, rax
	shr r10, 5
	mov rax, r11
	shl rax, 59
	or r10, rax
	shr r11, 5
	mov rax, r12
	shl rax, 59
	or r11, rax
	shr r12, 5
	mov rax, r13
	shl rax, 59
	or r12, rax
	shr r13, 5
	mov rax, r14
	shl rax, 59
	or r13, rax
	shr r14, 5
	mov rax, r15
	shl rax, 59
	or r14, rax
	shr r15, 5
	mov rax, rbp
	shl rax, 59
	or r15, rax
	shr rbp, 5
	mov rax, rsi
	shl rax, 59
	or rbp, rax
	shr rsi, 5
	add rbx, 5
	jmp 210f
29:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	mov rax, r15
	shl rax, 63
	or r14, rax
	shr r15, 1
	mov rax, rbp
	shl rax, 63
	or r15, rax
	shr rbp, 1
	mov rax, rsi
	shl rax, 63
	or rbp, rax
	shr rsi, 1
	add rbx, 1
210:
	cmp rbx, 577
	jb 28b
	mov r12, rsi
	mov esi, 1720
	mov edx, 424
	mov ecx, 424
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 3160
	mov ecx, 3160
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 2800
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -1080
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -1080
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 6120
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7840]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7848]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7856]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7864]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7872]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7880]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7888]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7896]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7904]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1936], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1944], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1952], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1960], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1968], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1976], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1984], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1992], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2000], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1936]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1936], rdx
	mov rdx, QWORD PTR [rdi+1944]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1944], rdx
	mov rdx, QWORD PTR [rdi+1952]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1952], rdx
	mov rdx, QWORD PTR [rdi+1960]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1960], rdx
	mov rdx, QWORD PTR [rdi+1968]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1968], rdx
	mov rdx, QWORD PTR [rdi+1976]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1976], rdx
	mov rdx, QWORD PTR [rdi+1984]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1984], rdx
	mov rdx, QWORD PTR [rdi+1992]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1992], rdx
	mov rdx, QWORD PTR [rdi+2000]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2000], rdx
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 5904
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 7840
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -5904
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+424]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+432]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+440]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+448]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+456]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+464]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+472]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+480]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+488]
	mov rax, QWORD PTR [rdi+3224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+7984], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+7992], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+8000], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+8008], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+8016], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+8024], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+8032], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+8040], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+8048], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+7984]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7984], rdx
	mov rdx, QWORD PTR [rdi+7992]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7992], rdx
	mov rdx, QWORD PTR [rdi+8000]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+8000], rdx
	mov rdx, QWORD PTR [rdi+8008]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+8008], rdx
	mov rdx, QWORD PTR [rdi+8016]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+8016], rdx
	mov rdx, QWORD PTR [rdi+8024]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+8024], rdx
	mov rdx, QWORD PTR [rdi+8032]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+8032], rdx
	mov rdx, QWORD PTR [rdi+8040]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+8040], rdx
	mov rdx, QWORD PTR [rdi+8048]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+8048], rdx
	add rdi, 7984
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7984
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1936]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1944]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1952]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1960]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1968]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1976]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1984]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1992]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2000]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+7840], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+7848], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+7856], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+7864], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+7872], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+7880], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+7888], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+7896], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+7904], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+7840]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7840], rdx
	mov rdx, QWORD PTR [rdi+7848]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7848], rdx
	mov rdx, QWORD PTR [rdi+7856]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7856], rdx
	mov rdx, QWORD PTR [rdi+7864]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7864], rdx
	mov rdx, QWORD PTR [rdi+7872]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7872], rdx
	mov rdx, QWORD PTR [rdi+7880]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7880], rdx
	mov rdx, QWORD PTR [rdi+7888]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7888], rdx
	mov rdx, QWORD PTR [rdi+7896]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7896], rdx
	mov rdx, QWORD PTR [rdi+7904]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7904], rdx
	add rdi, 7840
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -5976
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 5976
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 7840
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -5976
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 5976
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 5976
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7912
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7912]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7920]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7928]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7936]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7944]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7952]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7960]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+1992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7968]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7976]
	mov rax, QWORD PTR [rdi+2000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+7912], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+7920], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+7928], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+7936], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+7944], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+7952], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+7960], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+7968], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+7976], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+7912]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7912], rdx
	mov rdx, QWORD PTR [rdi+7920]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7920], rdx
	mov rdx, QWORD PTR [rdi+7928]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7928], rdx
	mov rdx, QWORD PTR [rdi+7936]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7936], rdx
	mov rdx, QWORD PTR [rdi+7944]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7944], rdx
	mov rdx, QWORD PTR [rdi+7952]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7952], rdx
	mov rdx, QWORD PTR [rdi+7960]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7960], rdx
	mov rdx, QWORD PTR [rdi+7968]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7968], rdx
	mov rdx, QWORD PTR [rdi+7976]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+7976], rdx
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 7912
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -6120
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 6120
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7912
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+6112], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+6120], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+6128], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+6136], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+6144], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+6152], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+6160], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+6168], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+6176], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+6184], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+6192], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+6200], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+6208], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+6216], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+6224], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+6232], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+6240], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+6248], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+6256], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+6264], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+6272], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+6280], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+6288], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+6296], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+6304], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+6312], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+6320], rax
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+1280], rax
	mov ebx, 1
213:
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	test rdx, rdx
	je 214f
	mov rdx, QWORD PTR [rdi+7984]
	or rdx, QWORD PTR [rdi+7992]
	or rdx, QWORD PTR [rdi+8000]
	or rdx, QWORD PTR [rdi+8008]
	or rdx, QWORD PTR [rdi+8016]
	or rdx, QWORD PTR [rdi+8024]
	or rdx, QWORD PTR [rdi+8032]
	or rdx, QWORD PTR [rdi+8040]
	or rdx, QWORD PTR [rdi+8048]
	test rdx, rdx
	je 216f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+8000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+8000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+8000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+8008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+8000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+8008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+7984]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+8000]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+8008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+8016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+7992]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+8000]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+8008]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+8016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+8000]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+8008]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+8016]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+8024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+8008]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+8016]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+8024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+8016]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+8024]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+8032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+8024]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+8032]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+8032]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+8040]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+8040]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+8048]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1792], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1800], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1808], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1816], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1824], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1832], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1840], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1848], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+1856], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1792]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1792], rdx
	mov rdx, QWORD PTR [rdi+1800]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1800], rdx
	mov rdx, QWORD PTR [rdi+1808]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1808], rdx
	mov rdx, QWORD PTR [rdi+1816]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1816], rdx
	mov rdx, QWORD PTR [rdi+1824]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1824], rdx
	mov rdx, QWORD PTR [rdi+1832]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1832], rdx
	mov rdx, QWORD PTR [rdi+1840]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1840], rdx
	mov rdx, QWORD PTR [rdi+1848]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1848], rdx
	mov rdx, QWORD PTR [rdi+1856]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1856], rdx
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7840]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1720]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7848]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1728]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7856]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1736]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7864]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1744]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7872]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1752]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7880]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1760]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7888]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1768]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7896]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1776]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1784]
	mov rax, QWORD PTR [rdi+7904]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1936], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1944], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1952], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1960], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1968], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1976], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1984], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1992], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2000], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1936]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1936], rdx
	mov rdx, QWORD PTR [rdi+1944]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1944], rdx
	mov rdx, QWORD PTR [rdi+1952]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1952], rdx
	mov rdx, QWORD PTR [rdi+1960]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1960], rdx
	mov rdx, QWORD PTR [rdi+1968]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1968], rdx
	mov rdx, QWORD PTR [rdi+1976]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1976], rdx
	mov rdx, QWORD PTR [rdi+1984]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1984], rdx
	mov rdx, QWORD PTR [rdi+1992]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1992], rdx
	mov rdx, QWORD PTR [rdi+2000]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2000], rdx
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2008], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2016], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2024], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2032], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2040], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2048], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2056], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2064], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2072], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2008]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2008], rdx
	mov rdx, QWORD PTR [rdi+2016]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2016], rdx
	mov rdx, QWORD PTR [rdi+2024]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2024], rdx
	mov rdx, QWORD PTR [rdi+2032]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2032], rdx
	mov rdx, QWORD PTR [rdi+2040]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2040], rdx
	mov rdx, QWORD PTR [rdi+2048]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2048], rdx
	mov rdx, QWORD PTR [rdi+2056]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2056], rdx
	mov rdx, QWORD PTR [rdi+2064]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2064], rdx
	mov rdx, QWORD PTR [rdi+2072]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2072], rdx
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7912]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1216]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7920]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1224]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7928]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1232]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7936]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1240]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7944]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1248]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7952]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+1256]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7960]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+1264]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7968]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+1272]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+1280]
	mov rax, QWORD PTR [rdi+7976]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2080], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2088], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2096], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2104], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2112], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2120], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2128], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2136], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2144], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2080]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2080], rdx
	mov rdx, QWORD PTR [rdi+2088]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2088], rdx
	mov rdx, QWORD PTR [rdi+2096]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2096], rdx
	mov rdx, QWORD PTR [rdi+2104]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2104], rdx
	mov rdx, QWORD PTR [rdi+2112]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2112], rdx
	mov rdx, QWORD PTR [rdi+2120]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2120], rdx
	mov rdx, QWORD PTR [rdi+2128]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2128], rdx
	mov rdx, QWORD PTR [rdi+2136]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2136], rdx
	mov rdx, QWORD PTR [rdi+2144]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2144], rdx
	mov r12, rsi
	mov esi, 2080
	mov edx, 2080
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2080
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	mov rdx, QWORD PTR [rdi+1936]
	or rdx, QWORD PTR [rdi+1944]
	or rdx, QWORD PTR [rdi+1952]
	or rdx, QWORD PTR [rdi+1960]
	or rdx, QWORD PTR [rdi+1968]
	or rdx, QWORD PTR [rdi+1976]
	or rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	test rdx, rdx
	je 218f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1864
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1288
	mov edx, 2080
	mov ecx, 2080
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1216]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+7984]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1224]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+7992]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1232]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8000]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1240]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8008]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1248]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8016]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1256]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+8024]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1264]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+8032]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1272]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+8040]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+8048]
	mov rax, QWORD PTR [rdi+1280]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1432], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1440], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1448], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1456], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1464], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1472], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1480], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1488], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+1496], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1432]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1432], rdx
	mov rdx, QWORD PTR [rdi+1440]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1440], rdx
	mov rdx, QWORD PTR [rdi+1448]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1448], rdx
	mov rdx, QWORD PTR [rdi+1456]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1456], rdx
	mov rdx, QWORD PTR [rdi+1464]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1464], rdx
	mov rdx, QWORD PTR [rdi+1472]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1472], rdx
	mov rdx, QWORD PTR [rdi+1480]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1480], rdx
	mov rdx, QWORD PTR [rdi+1488]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1488], rdx
	mov rdx, QWORD PTR [rdi+1496]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1496], rdx
	mov r12, rsi
	mov esi, 1432
	mov edx, 1432
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	jmp 219f
218:
	mov rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	or rdx, QWORD PTR [rdi+2112]
	or rdx, QWORD PTR [rdi+2120]
	or rdx, QWORD PTR [rdi+2128]
	or rdx, QWORD PTR [rdi+2136]
	or rdx, QWORD PTR [rdi+2144]
	test rdx, rdx
	je 220f
	movabs rax, 0
	mov QWORD PTR [rdi+1288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1496], rax
	jmp 221f
220:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
221:
219:
	jmp 217f
216:
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1216]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1224]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1232]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1240]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1248]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1256]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1264]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1272]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+1496], rax
217:
	jmp 215f
214:
	mov rax, QWORD PTR [rdi+7840]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+7848]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+7856]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+7864]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+7872]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+7880]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+7888]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+7896]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+7904]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+7912]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7920]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7928]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7936]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7944]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7952]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7960]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7968]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7976]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+7984]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+7992]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+8000]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+8008]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+8016]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+8024]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+8032]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+8040]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+8048]
	mov QWORD PTR [rdi+1496], rax
215:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1072]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1088]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1104]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1120]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1136]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1152]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1168]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1184]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1200]
	movdqu XMMWORD PTR [rdx+128], xmm8
	movdqu xmm9, XMMWORD PTR [rdi+1216]
	movdqu XMMWORD PTR [rdx+144], xmm9
	movdqu xmm10, XMMWORD PTR [rdi+1232]
	movdqu XMMWORD PTR [rdx+160], xmm10
	movdqu xmm11, XMMWORD PTR [rdi+1248]
	movdqu XMMWORD PTR [rdx+176], xmm11
	movdqu xmm12, XMMWORD PTR [rdi+1264]
	movdqu XMMWORD PTR [rdx+192], xmm12
	movdqu xmm13, XMMWORD PTR [rdi+1272]
	movdqu XMMWORD PTR [rdx+200], xmm13
	add rbx, 1
	cmp rbx, 8
	jb 213b
	mov ebx, 0
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm4
	mov r12, rsi
	mov esi, 1504
	mov edx, 1648
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1576
	mov edx, 1504
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov rax, rbx
	mov ecx, 144
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1504]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1520]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1536]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1552]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1568]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1584]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1600]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1616]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1632]
	movdqu XMMWORD PTR [rdx+128], xmm8
	add rbx, 1
	cmp rbx, 8
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov ebx, 577
222:
	sub rbx, 1
	cmp rbx, 576
	je 223f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	jmp 224f
223:
224:
	movzx r8d, BYTE PTR [rdi+rbx*1+5320]
	test r8, r8
	je 225f
	cmp r8, 128
	jb 227f
	mov eax, 256
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu xmm9, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu xmm10, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu xmm11, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu xmm12, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu xmm13, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rax, r8
	sub rax, 1
	mov ecx, 72
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+5968], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+5984], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6000], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6016], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6032], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6048], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+6064], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+6080], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+6096], xmm8
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1576
	jmp 228f
227:
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu xmm9, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu xmm10, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu xmm11, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu xmm12, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu xmm13, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rax, r8
	sub rax, 1
	mov ecx, 72
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+5968], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+5984], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6000], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6016], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6032], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6048], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+6064], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+6080], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+6096], xmm8
228:
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	test rdx, rdx
	je 229f
	mov rdx, QWORD PTR [rdi+1648]
	or rdx, QWORD PTR [rdi+1656]
	or rdx, QWORD PTR [rdi+1664]
	or rdx, QWORD PTR [rdi+1672]
	or rdx, QWORD PTR [rdi+1680]
	or rdx, QWORD PTR [rdi+1688]
	or rdx, QWORD PTR [rdi+1696]
	or rdx, QWORD PTR [rdi+1704]
	or rdx, QWORD PTR [rdi+1712]
	test rdx, rdx
	je 231f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5968]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+5976]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+5984]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1096]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+5992]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1104]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6000]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1112]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6008]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1120]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6016]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1128]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6024]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6032]
	mov rax, QWORD PTR [rdi+1136]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+1864], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+1872], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+1880], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+1888], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+1896], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+1904], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+1912], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+1920], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+1928], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+1864]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1864], rdx
	mov rdx, QWORD PTR [rdi+1872]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1872], rdx
	mov rdx, QWORD PTR [rdi+1880]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1880], rdx
	mov rdx, QWORD PTR [rdi+1888]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1888], rdx
	mov rdx, QWORD PTR [rdi+1896]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1896], rdx
	mov rdx, QWORD PTR [rdi+1904]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1904], rdx
	mov rdx, QWORD PTR [rdi+1912]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1912], rdx
	mov rdx, QWORD PTR [rdi+1920]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1920], rdx
	mov rdx, QWORD PTR [rdi+1928]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+1928], rdx
	mov r12, rsi
	mov esi, 1936
	mov edx, 1504
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1144]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6040]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1152]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6048]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1160]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6056]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1168]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6064]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1176]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6072]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1184]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+6080]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1192]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+6088]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1200]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+6096]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+6104]
	mov rax, QWORD PTR [rdi+1208]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2008], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2016], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2024], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2032], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2040], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2048], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2056], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2064], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2072], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2008]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2008], rdx
	mov rdx, QWORD PTR [rdi+2016]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2016], rdx
	mov rdx, QWORD PTR [rdi+2024]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2024], rdx
	mov rdx, QWORD PTR [rdi+2032]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2032], rdx
	mov rdx, QWORD PTR [rdi+2040]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2040], rdx
	mov rdx, QWORD PTR [rdi+2048]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2048], rdx
	mov rdx, QWORD PTR [rdi+2056]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2056], rdx
	mov rdx, QWORD PTR [rdi+2064]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2064], rdx
	mov rdx, QWORD PTR [rdi+2072]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2072], rdx
	mov r12, rsi
	mov esi, 2080
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 2080
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2080
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	mov rdx, QWORD PTR [rdi+1936]
	or rdx, QWORD PTR [rdi+1944]
	or rdx, QWORD PTR [rdi+1952]
	or rdx, QWORD PTR [rdi+1960]
	or rdx, QWORD PTR [rdi+1968]
	or rdx, QWORD PTR [rdi+1976]
	or rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	test rdx, rdx
	je 233f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1864
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1288
	mov edx, 2080
	mov ecx, 2080
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 1216
	mov ecx, 1648
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1432
	mov edx, 1432
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	jmp 234f
233:
	mov rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	or rdx, QWORD PTR [rdi+2112]
	or rdx, QWORD PTR [rdi+2120]
	or rdx, QWORD PTR [rdi+2128]
	or rdx, QWORD PTR [rdi+2136]
	or rdx, QWORD PTR [rdi+2144]
	test rdx, rdx
	je 235f
	movabs rax, 0
	mov QWORD PTR [rdi+1288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1496], rax
	jmp 236f
235:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
236:
234:
	jmp 232f
231:
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1216]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1224]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1232]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1240]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1248]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1256]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1264]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1272]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+1496], rax
232:
	jmp 230f
229:
	mov rax, QWORD PTR [rdi+1504]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1512]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1520]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1528]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1648]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1656]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1496], rax
230:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	jmp 226f
225:
226:
	movzx r8d, BYTE PTR [rdi+rbx*1+3304]
	test r8, r8
	je 237f
	cmp r8, 128
	jb 239f
	mov eax, 256
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	mov ecx, 144
	mul rcx
	lea rdx, {VG_P521_COMB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1712], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1576
	jmp 240f
239:
	mov rax, r8
	sub rax, 1
	mov ecx, 144
	mul rcx
	lea rdx, {VG_P521_COMB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1712], rax
240:
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	test rdx, rdx
	je 241f
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1864], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1872], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1880], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1888], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1896], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1904], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+1912], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+1920], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+1928], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+2008], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+2016], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+2024], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+2032], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+2040], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+2072], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1504
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 2080
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2080
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	mov rdx, QWORD PTR [rdi+1936]
	or rdx, QWORD PTR [rdi+1944]
	or rdx, QWORD PTR [rdi+1952]
	or rdx, QWORD PTR [rdi+1960]
	or rdx, QWORD PTR [rdi+1968]
	or rdx, QWORD PTR [rdi+1976]
	or rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	test rdx, rdx
	je 243f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1864
	mov ecx, 1720
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1288
	mov edx, 2080
	mov ecx, 2080
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 1216
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	jmp 244f
243:
	mov rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	or rdx, QWORD PTR [rdi+2112]
	or rdx, QWORD PTR [rdi+2120]
	or rdx, QWORD PTR [rdi+2128]
	or rdx, QWORD PTR [rdi+2136]
	or rdx, QWORD PTR [rdi+2144]
	test rdx, rdx
	je 245f
	movabs rax, 0
	mov QWORD PTR [rdi+1288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1496], rax
	jmp 246f
245:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
246:
244:
	jmp 242f
241:
	mov rax, QWORD PTR [rdi+1504]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1512]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1520]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1528]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1648]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1656]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1496], rax
242:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	jmp 238f
237:
238:
	test rbx, rbx
	jne 222b
	mov r12, rsi
	mov esi, 1216
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	movabs rax, 0
	mov QWORD PTR [rdi+2512], rax
	movabs rax, 70368744177664
	mov QWORD PTR [rdi+2520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2576], rax
	movabs rax, 360287970189639679
	mov QWORD PTR [rdi+2152], rax
	movabs rax, -2927982029091333070
	mov QWORD PTR [rdi+2160], rax
	movabs rax, -1720978806102766045
	mov QWORD PTR [rdi+2168], rax
	movabs rax, 3873067094995862738
	mov QWORD PTR [rdi+2176], rax
	movabs rax, -204699087262476341
	mov QWORD PTR [rdi+2184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2192], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2200], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2208], rax
	movabs rax, 511
	mov QWORD PTR [rdi+2216], rax
	movabs rax, 4940528924288850934
	mov QWORD PTR [rdi+136], rax
	movabs rax, -4302566813442262959
	mov QWORD PTR [rdi+144], rax
	movabs rax, -9208736750959699409
	mov QWORD PTR [rdi+152], rax
	movabs rax, -5874531763869423212
	mov QWORD PTR [rdi+160], rax
	movabs rax, 5
	mov QWORD PTR [rdi+168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+200], rax
	mov r9d, 0
	mov r10d, 0
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2296]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2512]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4024]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2304]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2520]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4032]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4024], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2312]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2528]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4040]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4032], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2320]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2536]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4048]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4040], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2328]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2544]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4056]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4048], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2336]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, QWORD PTR [rdi+2552]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4064]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4056], r10
	mov r10d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2344]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, QWORD PTR [rdi+2560]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4072]
	mul rcx
	add r11, rax
	adc r9, rdx
	adc r10, 0
	mov QWORD PTR [rdi+4064], r11
	mov r11d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2352]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, QWORD PTR [rdi+2568]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4080]
	mul rcx
	add r9, rax
	adc r10, rdx
	adc r11, 0
	mov QWORD PTR [rdi+4072], r9
	mov r9d, 0
	mov rcx, QWORD PTR [rdi+2576]
	mov rax, QWORD PTR [rdi+2360]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov rcx, 512
	mov rax, QWORD PTR [rdi+4088]
	mul rcx
	add r10, rax
	adc r11, rdx
	adc r9, 0
	mov QWORD PTR [rdi+4080], r10
	mov r10d, 0
	mov QWORD PTR [rdi+4088], r11
	mov r11d, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+2512], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+72]
	mov QWORD PTR [rdi+2520], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+80]
	mov QWORD PTR [rdi+2528], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+88]
	mov QWORD PTR [rdi+2536], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+96]
	mov QWORD PTR [rdi+2544], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+104]
	mov QWORD PTR [rdi+2552], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+112]
	mov QWORD PTR [rdi+2560], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+120]
	mov QWORD PTR [rdi+2568], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+128]
	mov QWORD PTR [rdi+2576], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2512]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2512], rdx
	mov rdx, QWORD PTR [rdi+2520]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2520], rdx
	mov rdx, QWORD PTR [rdi+2528]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2528], rdx
	mov rdx, QWORD PTR [rdi+2536]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2536], rdx
	mov rdx, QWORD PTR [rdi+2544]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2544], rdx
	mov rdx, QWORD PTR [rdi+2552]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2552], rdx
	mov rdx, QWORD PTR [rdi+2560]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2560], rdx
	mov rdx, QWORD PTR [rdi+2568]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2568], rdx
	mov rdx, QWORD PTR [rdi+2576]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2576], rdx
	mov r12, rsi
	mov esi, 2584
	mov edx, 2512
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1512
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2944
	add rdi, 2512
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2512
	mov r12, rsi
	mov esi, 2584
	mov edx, 2512
	mov ecx, 1216
	call {vg_p521_mul_mod_p}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1512
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2800
	mov rdx, QWORD PTR [rdi+2944]
	or rdx, QWORD PTR [rdi+2952]
	or rdx, QWORD PTR [rdi+2960]
	or rdx, QWORD PTR [rdi+2968]
	or rdx, QWORD PTR [rdi+2976]
	or rdx, QWORD PTR [rdi+2984]
	or rdx, QWORD PTR [rdi+2992]
	or rdx, QWORD PTR [rdi+3000]
	or rdx, QWORD PTR [rdi+3008]
	cmp rdx, 1
	sbb rdx, rdx
	mov rbp, rdx
	mov rdx, QWORD PTR [rdi+2296]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2304]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2312]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2320]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2328]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2336]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2344]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2352]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2360]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov r12, rax
	mov rdx, QWORD PTR [rdi+2800]
	or rdx, QWORD PTR [rdi+2808]
	or rdx, QWORD PTR [rdi+2816]
	or rdx, QWORD PTR [rdi+2824]
	or rdx, QWORD PTR [rdi+2832]
	or rdx, QWORD PTR [rdi+2840]
	or rdx, QWORD PTR [rdi+2848]
	or rdx, QWORD PTR [rdi+2856]
	or rdx, QWORD PTR [rdi+2864]
	cmp rdx, 1
	sbb rdx, rdx
	and rdx, r12
	or rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+3232]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ecdsa_p521_sign_adx:
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+58]
	bswap rax
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rcx+50]
	bswap rax
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rcx+42]
	bswap rax
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rcx+34]
	bswap rax
	mov QWORD PTR [rdi+2320], rax
	mov rax, QWORD PTR [rcx+26]
	bswap rax
	mov QWORD PTR [rdi+2328], rax
	mov rax, QWORD PTR [rcx+18]
	bswap rax
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rcx+10]
	bswap rax
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rcx+2]
	bswap rax
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2360], rax
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2504], rax
	mov rax, QWORD PTR [rdi+2440]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2448]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdi+2448]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2456]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdi+2456]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2464]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdi+2464]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2472]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdi+2472]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2480]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdi+2480]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2488]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdi+2488]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2496]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdi+2496]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2504]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdi+2504]
	shr rax, 7
	mov QWORD PTR [rdi+2504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -1
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -1
	mov QWORD PTR [rdi+120], rax
	movabs rax, 511
	mov QWORD PTR [rdi+128], rax
	movabs rax, -4940528924288850935
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+144], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+152], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+160], rax
	movabs rax, -6
	mov QWORD PTR [rdi+168], rax
	movabs rax, -1
	mov QWORD PTR [rdi+176], rax
	movabs rax, -1
	mov QWORD PTR [rdi+184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 511
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 1
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+416], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+488], rax
	movabs rax, -108086391056891905
	mov QWORD PTR [rdi+496], rax
	movabs rax, -1
	mov QWORD PTR [rdi+504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+512], rax
	movabs rax, -1
	mov QWORD PTR [rdi+520], rax
	movabs rax, -1
	mov QWORD PTR [rdi+528], rax
	movabs rax, -1
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 511
	mov QWORD PTR [rdi+560], rax
	movabs rax, -9206149359546586475
	mov QWORD PTR [rdi+568], rax
	movabs rax, 7703098954667325534
	mov QWORD PTR [rdi+576], rax
	movabs rax, -8444198932957117873
	mov QWORD PTR [rdi+584], rax
	movabs rax, 4080679219017386654
	mov QWORD PTR [rdi+592], rax
	movabs rax, -3314326249800548899
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1327138235749078642
	mov QWORD PTR [rdi+608], rax
	movabs rax, 7346575694218300576
	mov QWORD PTR [rdi+616], rax
	movabs rax, 3412575346494654433
	mov QWORD PTR [rdi+624], rax
	movabs rax, 231
	mov QWORD PTR [rdi+632], rax
	movabs rax, -5534465018312146687
	mov QWORD PTR [rdi+640], rax
	movabs rax, 5619576712772809438
	mov QWORD PTR [rdi+648], rax
	movabs rax, 8005610518557668641
	mov QWORD PTR [rdi+656], rax
	movabs rax, -7746456476338520108
	mov QWORD PTR [rdi+664], rax
	movabs rax, -2499315621146659924
	mov QWORD PTR [rdi+672], rax
	movabs rax, -7999496471265827170
	mov QWORD PTR [rdi+680], rax
	movabs rax, 2399910904520155098
	mov QWORD PTR [rdi+688], rax
	movabs rax, -1815197603150574886
	mov QWORD PTR [rdi+696], rax
	movabs rax, 116
	mov QWORD PTR [rdi+704], rax
	movabs rax, 2902022722397546126
	mov QWORD PTR [rdi+712], rax
	movabs rax, 2325088080057329843
	mov QWORD PTR [rdi+720], rax
	movabs rax, -5721086412136040095
	mov QWORD PTR [rdi+728], rax
	movabs rax, 2333612672179754627
	mov QWORD PTR [rdi+736], rax
	movabs rax, 1606649517559478803
	mov QWORD PTR [rdi+744], rax
	movabs rax, 3750328465540489011
	mov QWORD PTR [rdi+752], rax
	movabs rax, -1383596148691055198
	mov QWORD PTR [rdi+760], rax
	movabs rax, 157139108829216397
	mov QWORD PTR [rdi+768], rax
	movabs rax, 480
	mov QWORD PTR [rdi+776], rax
	movabs rax, 1404226216438127876
	mov QWORD PTR [rdi+784], rax
	movabs rax, -646342563601285469
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1344198287485662207
	mov QWORD PTR [rdi+800], rax
	movabs rax, -3210469545270092282
	mov QWORD PTR [rdi+808], rax
	movabs rax, -2491014132492810277
	mov QWORD PTR [rdi+816], rax
	movabs rax, -3462193604041806274
	mov QWORD PTR [rdi+824], rax
	movabs rax, 6614782218913277884
	mov QWORD PTR [rdi+832], rax
	movabs rax, 3282565375810407749
	mov QWORD PTR [rdi+840], rax
	movabs rax, 61
	mov QWORD PTR [rdi+848], rax
	movabs rax, -324259173170675712
	mov QWORD PTR [rdi+856], rax
	movabs rax, 2927982029091333069
	mov QWORD PTR [rdi+864], rax
	movabs rax, 1720978806102766044
	mov QWORD PTR [rdi+872], rax
	movabs rax, -3873067094995862739
	mov QWORD PTR [rdi+880], rax
	movabs rax, 204699087262476340
	mov QWORD PTR [rdi+888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+920], rax
	movabs rax, -3
	mov QWORD PTR [rdi+928], rax
	movabs rax, -1
	mov QWORD PTR [rdi+936], rax
	movabs rax, -1
	mov QWORD PTR [rdi+944], rax
	movabs rax, -1
	mov QWORD PTR [rdi+952], rax
	movabs rax, -1
	mov QWORD PTR [rdi+960], rax
	movabs rax, -1
	mov QWORD PTR [rdi+968], rax
	movabs rax, -1
	mov QWORD PTR [rdi+976], rax
	movabs rax, -1
	mov QWORD PTR [rdi+984], rax
	movabs rax, 511
	mov QWORD PTR [rdi+992], rax
	movabs rax, -4940528924288850937
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -6
	mov QWORD PTR [rdi+1032], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 511
	mov QWORD PTR [rdi+1064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	movabs rax, -1
	mov QWORD PTR [rdi+3232], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3888], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3889], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3890], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3891], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3892], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3893], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3894], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3895], dl
	add rbx, 1
	cmp rbx, 72
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+1000]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4472], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4473], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4474], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4475], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4476], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4477], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4478], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4479], dl
	add rbx, 1
	cmp rbx, 72
	jne 22b
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	movabs rax, -2911398454546468714
	mov QWORD PTR [rdi+1072], rax
	movabs rax, -2622805883304785837
	mov QWORD PTR [rdi+1080], rax
	movabs rax, -6758855595800436770
	mov QWORD PTR [rdi+1088], rax
	movabs rax, -3350014429734814130
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 9185203175476711091
	mov QWORD PTR [rdi+1104], rax
	movabs rax, -2793569313455226504
	mov QWORD PTR [rdi+1112], rax
	movabs rax, -9062608006907465467
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 3497699202216198480
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 458
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 5408250952697325544
	mov QWORD PTR [rdi+1144], rax
	movabs rax, -267932407593670216
	mov QWORD PTR [rdi+1152], rax
	movabs rax, -8885807591840917390
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 8614545525818659092
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 4212919814057000474
	mov QWORD PTR [rdi+1176], rax
	movabs rax, -7381687526187518677
	mov QWORD PTR [rdi+1184], rax
	movabs rax, -4256878057158064348
	mov QWORD PTR [rdi+1192], rax
	movabs rax, -2260134842321433193
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 209
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov eax, 0
	mov QWORD PTR [rdi+3880], rax
	mov ebx, 83
23:
	sub rbx, 1
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov rax, rbx
	mov ecx, 9216
	mul rcx
	lea rdx, {VG_P521_COMB}
	add rdx, rax
	vmovq xmm13, r8
	vpbroadcastd ymm13, xmm13
	mov ecx, 1
	vmovq xmm12, rcx
	vpbroadcastd ymm12, xmm12
	vmovdqa ymm14, ymm12
	vpxor ymm0, ymm0, ymm0
	vpxor ymm1, ymm1, ymm1
	vpxor ymm2, ymm2, ymm2
	vpxor ymm3, ymm3, ymm3
	vpxor ymm4, ymm4, ymm4
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+32]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+64]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+96]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+112]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+144]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+176]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+208]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+240]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+256]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+288]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+320]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+352]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+384]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+400]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+432]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+464]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+496]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+528]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+544]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+576]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+608]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+640]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+672]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+688]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+720]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+752]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+784]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+816]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+832]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+864]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+896]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+928]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+960]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+976]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1008]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1040]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1072]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1104]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1120]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1152]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1184]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1216]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1248]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1264]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1296]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1328]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1360]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1392]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1408]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1440]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1472]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1504]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1536]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1552]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1584]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1616]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1648]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1680]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1696]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1728]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1760]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1792]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1824]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1840]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1872]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1904]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1936]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1968]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+1984]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2016]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2048]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2080]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2112]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2128]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2160]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2192]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2224]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2256]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2272]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2304]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2336]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2368]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2400]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2416]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2448]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2480]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2512]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2544]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2560]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2592]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2624]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2656]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2688]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2704]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2736]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2768]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2800]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2832]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2848]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2880]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2912]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2944]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2976]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+2992]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3024]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3056]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3088]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3120]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3136]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3168]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3200]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3232]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3264]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3280]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3312]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3344]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3376]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3408]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3424]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3456]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3488]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3520]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3552]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3568]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3600]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3632]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3664]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3696]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3712]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3744]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3776]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3808]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3840]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3856]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3888]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3920]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3952]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+3984]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4000]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4032]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4064]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4096]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4128]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4144]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4176]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4208]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4240]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4272]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4288]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4320]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4352]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4384]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4416]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4432]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4464]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4496]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4528]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4560]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4576]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4608]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4640]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4672]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4704]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4720]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4752]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4784]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4816]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4848]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4864]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4896]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4928]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4960]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+4992]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5008]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5040]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5072]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5104]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5136]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5152]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5184]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5216]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5248]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5280]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5296]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5328]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5360]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5392]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5424]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5440]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5472]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5504]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5536]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5568]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5584]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5616]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5648]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5680]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5712]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5728]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5760]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5792]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5824]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5856]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5872]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5904]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5936]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+5968]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6000]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6016]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6048]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6080]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6112]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6144]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6160]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6192]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6224]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6256]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6288]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6304]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6336]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6368]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6400]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6432]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6448]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6480]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6512]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6544]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6576]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6592]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6624]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6656]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6688]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6720]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6736]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6768]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6800]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6832]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6864]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6880]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6912]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6944]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+6976]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7008]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7024]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7056]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7088]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7120]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7152]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7168]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7200]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7232]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7264]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7296]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7312]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7344]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7376]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7408]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7440]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7456]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7488]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7520]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7552]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7584]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7600]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7632]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7664]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7696]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7728]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7744]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7776]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7808]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7840]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7872]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7888]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7920]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7952]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+7984]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8016]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8032]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8064]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8096]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8128]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8160]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8176]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8208]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8240]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8272]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8304]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8320]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8352]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8384]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8416]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8448]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8464]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8496]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8528]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8560]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8592]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8608]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8640]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8672]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8704]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8736]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8752]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8784]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8816]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8848]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8880]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8896]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8928]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8960]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+8992]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9024]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9040]
	vpor ymm4, ymm4, ymm11
	vpcmpeqd ymm15, ymm14, ymm13
	vpaddd ymm14, ymm14, ymm12
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9072]
	vpor ymm0, ymm0, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9104]
	vpor ymm1, ymm1, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9136]
	vpor ymm2, ymm2, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9168]
	vpor ymm3, ymm3, ymm11
	vpand ymm11, ymm15, YMMWORD PTR [rdx+9184]
	vpor ymm4, ymm4, ymm11
	vmovdqu YMMWORD PTR [rdi+1504], ymm0
	vmovdqu YMMWORD PTR [rdi+1536], ymm1
	vmovdqu YMMWORD PTR [rdi+1568], ymm2
	vmovdqu YMMWORD PTR [rdi+1600], ymm3
	vmovdqu YMMWORD PTR [rdi+1616], ymm4
	vzeroupper
	mov rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	movabs rax, 36028797018963968
	and rax, rcx
	or rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1576], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1584], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1592], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1600], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1608], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1616], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1624], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1632], rax
	movabs rax, 0
	and rax, rcx
	or rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1640], rax
	xor rcx, -1
	movabs rax, 36028797018963968
	and rax, rcx
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	and rax, rcx
	mov QWORD PTR [rdi+1712], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2224
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	movzx eax, BYTE PTR [rdi+rcx*1+3310]
	sub rax, 1
	mov rcx, rax
	mov rax, QWORD PTR [rdi+1576]
	mov rdx, QWORD PTR [rdi+2224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1576], rax
	mov rax, QWORD PTR [rdi+1584]
	mov rdx, QWORD PTR [rdi+2232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1584], rax
	mov rax, QWORD PTR [rdi+1592]
	mov rdx, QWORD PTR [rdi+2240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1592], rax
	mov rax, QWORD PTR [rdi+1600]
	mov rdx, QWORD PTR [rdi+2248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1600], rax
	mov rax, QWORD PTR [rdi+1608]
	mov rdx, QWORD PTR [rdi+2256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1608], rax
	mov rax, QWORD PTR [rdi+1616]
	mov rdx, QWORD PTR [rdi+2264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1616], rax
	mov rax, QWORD PTR [rdi+1624]
	mov rdx, QWORD PTR [rdi+2272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1624], rax
	mov rax, QWORD PTR [rdi+1632]
	mov rdx, QWORD PTR [rdi+2280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1632], rax
	mov rax, QWORD PTR [rdi+1640]
	mov rdx, QWORD PTR [rdi+2288]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1640], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1072
	mov ecx, 1504
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1576
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1504
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 2008
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	mov r12, rsi
	mov esi, 2008
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 2008
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -864
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 1360
	mov edx, 1504
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -288
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 2944
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 144
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1360
	mov edx, 2944
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1216
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 576
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 432
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -432
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 72
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	add rdi, 1720
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 144
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1720
	mov r12, rsi
	mov esi, 1792
	mov edx, 2008
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1720
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1360
	mov edx, 1288
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1432
	mov edx, 2008
	mov ecx, 1432
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1936
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov rax, rbx
	mov ecx, 7
	mul rcx
	mov rcx, rax
	mov eax, 0
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3310]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3309]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3308]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3307]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3306]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3305]
	add rax, rdx
	add rax, rax
	movzx edx, BYTE PTR [rdi+rcx*1+3304]
	add rax, rdx
	sub rax, 64
	mov rdx, rax
	shr rdx, 63
	mov r8d, 0
	sub r8, rdx
	xor rax, r8
	sub rax, r8
	mov r8, rax
	mov ecx, 0
	xor rcx, r8
	cmp rcx, 1
	sbb rcx, rcx
	mov rax, QWORD PTR [rdi+1288]
	mov rdx, QWORD PTR [rdi+1072]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov rdx, QWORD PTR [rdi+1080]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov rdx, QWORD PTR [rdi+1088]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov rdx, QWORD PTR [rdi+1096]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov rdx, QWORD PTR [rdi+1104]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov rdx, QWORD PTR [rdi+1112]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov rdx, QWORD PTR [rdi+1120]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov rdx, QWORD PTR [rdi+1128]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov rdx, QWORD PTR [rdi+1136]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov rdx, QWORD PTR [rdi+1144]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov rdx, QWORD PTR [rdi+1152]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov rdx, QWORD PTR [rdi+1160]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov rdx, QWORD PTR [rdi+1168]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov rdx, QWORD PTR [rdi+1176]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov rdx, QWORD PTR [rdi+1184]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov rdx, QWORD PTR [rdi+1192]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov rdx, QWORD PTR [rdi+1200]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov rdx, QWORD PTR [rdi+1208]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov rdx, QWORD PTR [rdi+1216]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov rdx, QWORD PTR [rdi+1224]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov rdx, QWORD PTR [rdi+1232]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov rdx, QWORD PTR [rdi+1240]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov rdx, QWORD PTR [rdi+1248]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov rdx, QWORD PTR [rdi+1256]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov rdx, QWORD PTR [rdi+1264]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov rdx, QWORD PTR [rdi+1272]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov rdx, QWORD PTR [rdi+1280]
	xor rdx, rax
	and rdx, rcx
	xor rax, rdx
	mov QWORD PTR [rdi+1280], rax
	test rbx, rbx
	jne 23b
	call {vg_p521_inv_mod_p_adx}
	add rdi, 2152
	mov rdx, QWORD PTR [rdi-1080]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1872], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-1072]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1880], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-1064]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1888], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-1056]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1896], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-1048]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1904], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-1040]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1912], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-1032]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1920], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-1024]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1928], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-1016]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1936], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1872
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1512
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2512
	add rdi, 352
	mov rdx, QWORD PTR [rdi+2160]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3672], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi+2168]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+3680], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi+2176]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+3688], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi+2184]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+3696], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi+2192]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+3704], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi+2200]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+3712], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi+2208]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+3720], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi+2216]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+3728], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi+2224]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+3736], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 3672
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1440
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2584
	mov r9d, 0
	mov r8, QWORD PTR [rdi+2584]
	add r8, QWORD PTR [rdi+280]
	mov QWORD PTR [rdi+4024], r8
	mov r8, QWORD PTR [rdi+2592]
	adc r8, QWORD PTR [rdi+288]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+2600]
	adc r8, QWORD PTR [rdi+296]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+2608]
	adc r8, QWORD PTR [rdi+304]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+2616]
	adc r8, QWORD PTR [rdi+312]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+2624]
	adc r8, QWORD PTR [rdi+320]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+2632]
	adc r8, QWORD PTR [rdi+328]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+2640]
	adc r8, QWORD PTR [rdi+336]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+2648]
	adc r8, QWORD PTR [rdi+344]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+2656], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+2664], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+2672], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+2680], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+2688], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+2696], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+2704], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+2712], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+2720], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+2656]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2656], rdx
	mov rdx, QWORD PTR [rdi+2664]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2664], rdx
	mov rdx, QWORD PTR [rdi+2672]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2672], rdx
	mov rdx, QWORD PTR [rdi+2680]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2680], rdx
	mov rdx, QWORD PTR [rdi+2688]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2688], rdx
	mov rdx, QWORD PTR [rdi+2696]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2696], rdx
	mov rdx, QWORD PTR [rdi+2704]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2704], rdx
	mov rdx, QWORD PTR [rdi+2712]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2712], rdx
	mov rdx, QWORD PTR [rdi+2720]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+2720], rdx
	mov r12, rsi
	mov esi, 2728
	mov edx, 2296
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+2368]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2376]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2384]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2392]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2400]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2408]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2416]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2424]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2432]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2368]
	or rdx, QWORD PTR [rdi+2376]
	or rdx, QWORD PTR [rdi+2384]
	or rdx, QWORD PTR [rdi+2392]
	or rdx, QWORD PTR [rdi+2400]
	or rdx, QWORD PTR [rdi+2408]
	or rdx, QWORD PTR [rdi+2416]
	or rdx, QWORD PTR [rdi+2424]
	or rdx, QWORD PTR [rdi+2432]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2296]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2304]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2312]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2320]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2328]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2336]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2344]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2352]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2360]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2296]
	or rdx, QWORD PTR [rdi+2304]
	or rdx, QWORD PTR [rdi+2312]
	or rdx, QWORD PTR [rdi+2320]
	or rdx, QWORD PTR [rdi+2328]
	or rdx, QWORD PTR [rdi+2336]
	or rdx, QWORD PTR [rdi+2344]
	or rdx, QWORD PTR [rdi+2352]
	or rdx, QWORD PTR [rdi+2360]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2656]
	or rdx, QWORD PTR [rdi+2664]
	or rdx, QWORD PTR [rdi+2672]
	or rdx, QWORD PTR [rdi+2680]
	or rdx, QWORD PTR [rdi+2688]
	or rdx, QWORD PTR [rdi+2696]
	or rdx, QWORD PTR [rdi+2704]
	or rdx, QWORD PTR [rdi+2712]
	or rdx, QWORD PTR [rdi+2720]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	call {vg_p521_inv_mod_n}
	mov r12, rsi
	mov esi, 2800
	mov edx, 2656
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2872
	mov edx, 2368
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2944
	mov edx, 2440
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2800
	mov ecx, 2872
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r9d, 0
	mov r8, QWORD PTR [rdi+3016]
	add r8, QWORD PTR [rdi+2944]
	mov QWORD PTR [rdi+4024], r8
	mov r8, QWORD PTR [rdi+3024]
	adc r8, QWORD PTR [rdi+2952]
	mov QWORD PTR [rdi+4032], r8
	mov r8, QWORD PTR [rdi+3032]
	adc r8, QWORD PTR [rdi+2960]
	mov QWORD PTR [rdi+4040], r8
	mov r8, QWORD PTR [rdi+3040]
	adc r8, QWORD PTR [rdi+2968]
	mov QWORD PTR [rdi+4048], r8
	mov r8, QWORD PTR [rdi+3048]
	adc r8, QWORD PTR [rdi+2976]
	mov QWORD PTR [rdi+4056], r8
	mov r8, QWORD PTR [rdi+3056]
	adc r8, QWORD PTR [rdi+2984]
	mov QWORD PTR [rdi+4064], r8
	mov r8, QWORD PTR [rdi+3064]
	adc r8, QWORD PTR [rdi+2992]
	mov QWORD PTR [rdi+4072], r8
	mov r8, QWORD PTR [rdi+3072]
	adc r8, QWORD PTR [rdi+3000]
	mov QWORD PTR [rdi+4080], r8
	mov r8, QWORD PTR [rdi+3080]
	adc r8, QWORD PTR [rdi+3008]
	mov QWORD PTR [rdi+4088], r8
	adc r9, 0
	mov r8, QWORD PTR [rdi+4024]
	sub r8, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+3016], r8
	mov r8, QWORD PTR [rdi+4032]
	sbb r8, QWORD PTR [rdi+144]
	mov QWORD PTR [rdi+3024], r8
	mov r8, QWORD PTR [rdi+4040]
	sbb r8, QWORD PTR [rdi+152]
	mov QWORD PTR [rdi+3032], r8
	mov r8, QWORD PTR [rdi+4048]
	sbb r8, QWORD PTR [rdi+160]
	mov QWORD PTR [rdi+3040], r8
	mov r8, QWORD PTR [rdi+4056]
	sbb r8, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+3048], r8
	mov r8, QWORD PTR [rdi+4064]
	sbb r8, QWORD PTR [rdi+176]
	mov QWORD PTR [rdi+3056], r8
	mov r8, QWORD PTR [rdi+4072]
	sbb r8, QWORD PTR [rdi+184]
	mov QWORD PTR [rdi+3064], r8
	mov r8, QWORD PTR [rdi+4080]
	sbb r8, QWORD PTR [rdi+192]
	mov QWORD PTR [rdi+3072], r8
	mov r8, QWORD PTR [rdi+4088]
	sbb r8, QWORD PTR [rdi+200]
	mov QWORD PTR [rdi+3080], r8
	mov rax, r9
	sbb rax, 0
	sbb rax, rax
	xor rax, -1
	mov rdx, QWORD PTR [rdi+3016]
	mov r8, QWORD PTR [rdi+4024]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3016], rdx
	mov rdx, QWORD PTR [rdi+3024]
	mov r8, QWORD PTR [rdi+4032]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3024], rdx
	mov rdx, QWORD PTR [rdi+3032]
	mov r8, QWORD PTR [rdi+4040]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3032], rdx
	mov rdx, QWORD PTR [rdi+3040]
	mov r8, QWORD PTR [rdi+4048]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3040], rdx
	mov rdx, QWORD PTR [rdi+3048]
	mov r8, QWORD PTR [rdi+4056]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3048], rdx
	mov rdx, QWORD PTR [rdi+3056]
	mov r8, QWORD PTR [rdi+4064]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3056], rdx
	mov rdx, QWORD PTR [rdi+3064]
	mov r8, QWORD PTR [rdi+4072]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3064], rdx
	mov rdx, QWORD PTR [rdi+3072]
	mov r8, QWORD PTR [rdi+4080]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3072], rdx
	mov rdx, QWORD PTR [rdi+3080]
	mov r8, QWORD PTR [rdi+4088]
	xor rdx, r8
	and rdx, rax
	xor rdx, r8
	mov QWORD PTR [rdi+3080], rdx
	mov r12, rsi
	mov esi, 3088
	mov edx, 2152
	mov ecx, 3016
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3160
	mov edx, 3088
	mov ecx, 352
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov rdx, QWORD PTR [rdi+3160]
	or rdx, QWORD PTR [rdi+3168]
	or rdx, QWORD PTR [rdi+3176]
	or rdx, QWORD PTR [rdi+3184]
	or rdx, QWORD PTR [rdi+3192]
	or rdx, QWORD PTR [rdi+3200]
	or rdx, QWORD PTR [rdi+3208]
	or rdx, QWORD PTR [rdi+3216]
	or rdx, QWORD PTR [rdi+3224]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rcx, QWORD PTR [rdi+3232]
	mov rax, QWORD PTR [rdi+2656]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+58], rax
	mov rax, QWORD PTR [rdi+2664]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+50], rax
	mov rax, QWORD PTR [rdi+2672]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+42], rax
	mov rax, QWORD PTR [rdi+2680]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+34], rax
	mov rax, QWORD PTR [rdi+2688]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+26], rax
	mov rax, QWORD PTR [rdi+2696]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+18], rax
	mov rax, QWORD PTR [rdi+2704]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+10], rax
	mov rax, QWORD PTR [rdi+2712]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+2], rax
	mov rax, QWORD PTR [rdi+2720]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi], dl
	mov rdx, rax
	mov BYTE PTR [rsi+1], dl
	mov rax, QWORD PTR [rdi+3160]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+124], rax
	mov rax, QWORD PTR [rdi+3168]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+116], rax
	mov rax, QWORD PTR [rdi+3176]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+108], rax
	mov rax, QWORD PTR [rdi+3184]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+100], rax
	mov rax, QWORD PTR [rdi+3192]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+92], rax
	mov rax, QWORD PTR [rdi+3200]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+84], rax
	mov rax, QWORD PTR [rdi+3208]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+76], rax
	mov rax, QWORD PTR [rdi+3216]
	and rax, rcx
	bswap rax
	mov QWORD PTR [rsi+68], rax
	mov rax, QWORD PTR [rdi+3224]
	and rax, rcx
	mov rdx, rax
	shr rdx, 8
	mov BYTE PTR [rsi+66], dl
	mov rdx, rax
	mov BYTE PTR [rsi+67], dl
	mov rax, rcx
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6

vg_ecdsa_p521_verify_adx:
	mov r8, rcx
	mov r9, rdi
	mov rcx, rdx
	mov r10, rdx
	add r10, 66
	mov rdx, rdi
	add rdx, 1
	mov QWORD PTR [r8], rbx
	mov QWORD PTR [r8+8], rbp
	mov QWORD PTR [r8+16], r12
	mov QWORD PTR [r8+24], r13
	mov QWORD PTR [r8+32], r14
	mov QWORD PTR [r8+40], r15
	mov r14, rdi
	mov rdi, r8
	mov rax, QWORD PTR [rcx+58]
	bswap rax
	mov QWORD PTR [rdi+2296], rax
	mov rax, QWORD PTR [rcx+50]
	bswap rax
	mov QWORD PTR [rdi+2304], rax
	mov rax, QWORD PTR [rcx+42]
	bswap rax
	mov QWORD PTR [rdi+2312], rax
	mov rax, QWORD PTR [rcx+34]
	bswap rax
	mov QWORD PTR [rdi+2320], rax
	mov rax, QWORD PTR [rcx+26]
	bswap rax
	mov QWORD PTR [rdi+2328], rax
	mov rax, QWORD PTR [rcx+18]
	bswap rax
	mov QWORD PTR [rdi+2336], rax
	mov rax, QWORD PTR [rcx+10]
	bswap rax
	mov QWORD PTR [rdi+2344], rax
	mov rax, QWORD PTR [rcx+2]
	bswap rax
	mov QWORD PTR [rdi+2352], rax
	mov rax, QWORD PTR [rcx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2360], rax
	mov rax, QWORD PTR [rsi+58]
	bswap rax
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rsi+50]
	bswap rax
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rsi+42]
	bswap rax
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rsi+34]
	bswap rax
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rsi+26]
	bswap rax
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rsi+18]
	bswap rax
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rsi+10]
	bswap rax
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rsi+2]
	bswap rax
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rsi]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2432], rax
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2440], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2448], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2456], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2464], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2472], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2480], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2488], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2496], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2504], rax
	mov rax, QWORD PTR [rdi+2368]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2376]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2368], rax
	mov rax, QWORD PTR [rdi+2376]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2384]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2376], rax
	mov rax, QWORD PTR [rdi+2384]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2392]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2384], rax
	mov rax, QWORD PTR [rdi+2392]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2400]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2392], rax
	mov rax, QWORD PTR [rdi+2400]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2408]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2400], rax
	mov rax, QWORD PTR [rdi+2408]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2416]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2408], rax
	mov rax, QWORD PTR [rdi+2416]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2424]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2416], rax
	mov rax, QWORD PTR [rdi+2424]
	shr rax, 7
	mov rdx, QWORD PTR [rdi+2432]
	and rdx, 127
	ror rdx, 7
	or rax, rdx
	mov QWORD PTR [rdi+2424], rax
	mov rax, QWORD PTR [rdi+2432]
	shr rax, 7
	mov QWORD PTR [rdi+2432], rax
	movabs rax, -1
	mov QWORD PTR [rdi+64], rax
	movabs rax, -1
	mov QWORD PTR [rdi+72], rax
	movabs rax, -1
	mov QWORD PTR [rdi+80], rax
	movabs rax, -1
	mov QWORD PTR [rdi+88], rax
	movabs rax, -1
	mov QWORD PTR [rdi+96], rax
	movabs rax, -1
	mov QWORD PTR [rdi+104], rax
	movabs rax, -1
	mov QWORD PTR [rdi+112], rax
	movabs rax, -1
	mov QWORD PTR [rdi+120], rax
	movabs rax, 511
	mov QWORD PTR [rdi+128], rax
	movabs rax, -4940528924288850935
	mov QWORD PTR [rdi+136], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+144], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+152], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+160], rax
	movabs rax, -6
	mov QWORD PTR [rdi+168], rax
	movabs rax, -1
	mov QWORD PTR [rdi+176], rax
	movabs rax, -1
	mov QWORD PTR [rdi+184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+192], rax
	movabs rax, 511
	mov QWORD PTR [rdi+200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+280], rax
	movabs rax, 0
	mov QWORD PTR [rdi+288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+344], rax
	movabs rax, 1
	mov QWORD PTR [rdi+352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+416], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+488], rax
	movabs rax, -108086391056891905
	mov QWORD PTR [rdi+496], rax
	movabs rax, -1
	mov QWORD PTR [rdi+504], rax
	movabs rax, -1
	mov QWORD PTR [rdi+512], rax
	movabs rax, -1
	mov QWORD PTR [rdi+520], rax
	movabs rax, -1
	mov QWORD PTR [rdi+528], rax
	movabs rax, -1
	mov QWORD PTR [rdi+536], rax
	movabs rax, -1
	mov QWORD PTR [rdi+544], rax
	movabs rax, -1
	mov QWORD PTR [rdi+552], rax
	movabs rax, 511
	mov QWORD PTR [rdi+560], rax
	movabs rax, -9206149359546586475
	mov QWORD PTR [rdi+568], rax
	movabs rax, 7703098954667325534
	mov QWORD PTR [rdi+576], rax
	movabs rax, -8444198932957117873
	mov QWORD PTR [rdi+584], rax
	movabs rax, 4080679219017386654
	mov QWORD PTR [rdi+592], rax
	movabs rax, -3314326249800548899
	mov QWORD PTR [rdi+600], rax
	movabs rax, -1327138235749078642
	mov QWORD PTR [rdi+608], rax
	movabs rax, 7346575694218300576
	mov QWORD PTR [rdi+616], rax
	movabs rax, 3412575346494654433
	mov QWORD PTR [rdi+624], rax
	movabs rax, 231
	mov QWORD PTR [rdi+632], rax
	movabs rax, -5534465018312146687
	mov QWORD PTR [rdi+640], rax
	movabs rax, 5619576712772809438
	mov QWORD PTR [rdi+648], rax
	movabs rax, 8005610518557668641
	mov QWORD PTR [rdi+656], rax
	movabs rax, -7746456476338520108
	mov QWORD PTR [rdi+664], rax
	movabs rax, -2499315621146659924
	mov QWORD PTR [rdi+672], rax
	movabs rax, -7999496471265827170
	mov QWORD PTR [rdi+680], rax
	movabs rax, 2399910904520155098
	mov QWORD PTR [rdi+688], rax
	movabs rax, -1815197603150574886
	mov QWORD PTR [rdi+696], rax
	movabs rax, 116
	mov QWORD PTR [rdi+704], rax
	movabs rax, 2902022722397546126
	mov QWORD PTR [rdi+712], rax
	movabs rax, 2325088080057329843
	mov QWORD PTR [rdi+720], rax
	movabs rax, -5721086412136040095
	mov QWORD PTR [rdi+728], rax
	movabs rax, 2333612672179754627
	mov QWORD PTR [rdi+736], rax
	movabs rax, 1606649517559478803
	mov QWORD PTR [rdi+744], rax
	movabs rax, 3750328465540489011
	mov QWORD PTR [rdi+752], rax
	movabs rax, -1383596148691055198
	mov QWORD PTR [rdi+760], rax
	movabs rax, 157139108829216397
	mov QWORD PTR [rdi+768], rax
	movabs rax, 480
	mov QWORD PTR [rdi+776], rax
	movabs rax, 1404226216438127876
	mov QWORD PTR [rdi+784], rax
	movabs rax, -646342563601285469
	mov QWORD PTR [rdi+792], rax
	movabs rax, 1344198287485662207
	mov QWORD PTR [rdi+800], rax
	movabs rax, -3210469545270092282
	mov QWORD PTR [rdi+808], rax
	movabs rax, -2491014132492810277
	mov QWORD PTR [rdi+816], rax
	movabs rax, -3462193604041806274
	mov QWORD PTR [rdi+824], rax
	movabs rax, 6614782218913277884
	mov QWORD PTR [rdi+832], rax
	movabs rax, 3282565375810407749
	mov QWORD PTR [rdi+840], rax
	movabs rax, 61
	mov QWORD PTR [rdi+848], rax
	movabs rax, -324259173170675712
	mov QWORD PTR [rdi+856], rax
	movabs rax, 2927982029091333069
	mov QWORD PTR [rdi+864], rax
	movabs rax, 1720978806102766044
	mov QWORD PTR [rdi+872], rax
	movabs rax, -3873067094995862739
	mov QWORD PTR [rdi+880], rax
	movabs rax, 204699087262476340
	mov QWORD PTR [rdi+888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+920], rax
	movabs rax, -3
	mov QWORD PTR [rdi+928], rax
	movabs rax, -1
	mov QWORD PTR [rdi+936], rax
	movabs rax, -1
	mov QWORD PTR [rdi+944], rax
	movabs rax, -1
	mov QWORD PTR [rdi+952], rax
	movabs rax, -1
	mov QWORD PTR [rdi+960], rax
	movabs rax, -1
	mov QWORD PTR [rdi+968], rax
	movabs rax, -1
	mov QWORD PTR [rdi+976], rax
	movabs rax, -1
	mov QWORD PTR [rdi+984], rax
	movabs rax, 511
	mov QWORD PTR [rdi+992], rax
	movabs rax, -4940528924288850937
	mov QWORD PTR [rdi+1000], rax
	movabs rax, 4302566813442262958
	mov QWORD PTR [rdi+1008], rax
	movabs rax, 9208736750959699408
	mov QWORD PTR [rdi+1016], rax
	movabs rax, 5874531763869423211
	mov QWORD PTR [rdi+1024], rax
	movabs rax, -6
	mov QWORD PTR [rdi+1032], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1040], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1048], rax
	movabs rax, -1
	mov QWORD PTR [rdi+1056], rax
	movabs rax, 511
	mov QWORD PTR [rdi+1064], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	movabs rax, -1
	mov QWORD PTR [rdi+3232], rax
	mov rsi, r14
	mov ebx, 0
20:
	movzx eax, BYTE PTR [rdi+rbx*1+2296]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3304], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3305], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3306], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3307], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3308], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3309], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3310], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3311], dl
	add rbx, 1
	cmp rbx, 72
	jne 20b
	mov ebx, 0
21:
	movzx eax, BYTE PTR [rdi+rbx*1+928]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3888], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3889], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3890], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3891], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3892], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3893], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3894], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+3895], dl
	add rbx, 1
	cmp rbx, 72
	jne 21b
	mov ebx, 0
22:
	movzx eax, BYTE PTR [rdi+rbx*1+1000]
	mov rdx, rax
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4472], dl
	mov rdx, rax
	shr rdx, 1
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4473], dl
	mov rdx, rax
	shr rdx, 2
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4474], dl
	mov rdx, rax
	shr rdx, 3
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4475], dl
	mov rdx, rax
	shr rdx, 4
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4476], dl
	mov rdx, rax
	shr rdx, 5
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4477], dl
	mov rdx, rax
	shr rdx, 6
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4478], dl
	mov rdx, rax
	shr rdx, 7
	and rdx, 1
	mov BYTE PTR [rdi+rbx*8+4479], dl
	add rbx, 1
	cmp rbx, 72
	jne 22b
	mov rax, QWORD PTR [r10+58]
	bswap rax
	mov QWORD PTR [rdi+2224], rax
	mov rax, QWORD PTR [r10+50]
	bswap rax
	mov QWORD PTR [rdi+2232], rax
	mov rax, QWORD PTR [r10+42]
	bswap rax
	mov QWORD PTR [rdi+2240], rax
	mov rax, QWORD PTR [r10+34]
	bswap rax
	mov QWORD PTR [rdi+2248], rax
	mov rax, QWORD PTR [r10+26]
	bswap rax
	mov QWORD PTR [rdi+2256], rax
	mov rax, QWORD PTR [r10+18]
	bswap rax
	mov QWORD PTR [rdi+2264], rax
	mov rax, QWORD PTR [r10+10]
	bswap rax
	mov QWORD PTR [rdi+2272], rax
	mov rax, QWORD PTR [r10+2]
	bswap rax
	mov QWORD PTR [rdi+2280], rax
	mov rax, QWORD PTR [r10]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2872], rax
	movabs rax, 70368744177664
	mov QWORD PTR [rdi+2880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2896], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2904], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2912], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2920], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2928], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2936], rax
	movabs rax, -9217631144418712697
	mov QWORD PTR [rdi+2944], rax
	movabs rax, 8716614342792292383
	mov QWORD PTR [rdi+2952], rax
	movabs rax, -8963647668888889830
	mov QWORD PTR [rdi+2960], rax
	movabs rax, -4788688284897388321
	mov QWORD PTR [rdi+2968], rax
	movabs rax, -1104775416600182967
	mov QWORD PTR [rdi+2976], rax
	movabs rax, -442379411916359548
	mov QWORD PTR [rdi+2984], rax
	movabs rax, 8597773255975950730
	mov QWORD PTR [rdi+2992], rax
	movabs rax, 1137525115498218144
	mov QWORD PTR [rdi+3000], rax
	movabs rax, 77
	mov QWORD PTR [rdi+3008], rax
	mov rdx, r9
	add rdx, 67
	mov rax, QWORD PTR [rdx+58]
	bswap rax
	mov QWORD PTR [rdi+2656], rax
	mov rax, QWORD PTR [rdx+50]
	bswap rax
	mov QWORD PTR [rdi+2664], rax
	mov rax, QWORD PTR [rdx+42]
	bswap rax
	mov QWORD PTR [rdi+2672], rax
	mov rax, QWORD PTR [rdx+34]
	bswap rax
	mov QWORD PTR [rdi+2680], rax
	mov rax, QWORD PTR [rdx+26]
	bswap rax
	mov QWORD PTR [rdi+2688], rax
	mov rax, QWORD PTR [rdx+18]
	bswap rax
	mov QWORD PTR [rdi+2696], rax
	mov rax, QWORD PTR [rdx+10]
	bswap rax
	mov QWORD PTR [rdi+2704], rax
	mov rax, QWORD PTR [rdx+2]
	bswap rax
	mov QWORD PTR [rdi+2712], rax
	mov rax, QWORD PTR [rdx]
	bswap rax
	shr rax, 48
	mov QWORD PTR [rdi+2720], rax
	movzx edx, BYTE PTR [r9]
	xor rdx, 4
	cmp rdx, 1
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	call {vg_p521_check_point_adx}
	mov rdx, QWORD PTR [rdi+2296]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2304]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2312]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2320]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2328]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2336]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2344]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2352]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2360]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2296]
	or rdx, QWORD PTR [rdi+2304]
	or rdx, QWORD PTR [rdi+2312]
	or rdx, QWORD PTR [rdi+2320]
	or rdx, QWORD PTR [rdi+2328]
	or rdx, QWORD PTR [rdi+2336]
	or rdx, QWORD PTR [rdi+2344]
	or rdx, QWORD PTR [rdi+2352]
	or rdx, QWORD PTR [rdi+2360]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+2224]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2232]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2240]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2248]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2256]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2264]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2272]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2280]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2288]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov rbp, rax
	mov rdx, QWORD PTR [rdi+2224]
	or rdx, QWORD PTR [rdi+2232]
	or rdx, QWORD PTR [rdi+2240]
	or rdx, QWORD PTR [rdi+2248]
	or rdx, QWORD PTR [rdi+2256]
	or rdx, QWORD PTR [rdi+2264]
	or rdx, QWORD PTR [rdi+2272]
	or rdx, QWORD PTR [rdi+2280]
	or rdx, QWORD PTR [rdi+2288]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	and rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov r12, rsi
	mov esi, 2728
	mov edx, 2224
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	call {vg_p521_inv_mod_n}
	mov r12, rsi
	mov esi, 2944
	mov edx, 2368
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2872
	mov edx, 2296
	mov ecx, 784
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3016
	mov edx, 2944
	mov ecx, 2152
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 3088
	mov edx, 2872
	mov ecx, 2152
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2512
	mov edx, 3016
	mov ecx, 352
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2584
	mov edx, 3088
	mov ecx, 352
	call {vg_p521_mul_mod_n}
	mov rsi, r12
	mov r8, QWORD PTR [rdi+2512]
	mov r9, QWORD PTR [rdi+2520]
	mov r10, QWORD PTR [rdi+2528]
	mov r11, QWORD PTR [rdi+2536]
	mov r12, QWORD PTR [rdi+2544]
	mov r13, QWORD PTR [rdi+2552]
	mov r14, QWORD PTR [rdi+2560]
	mov r15, QWORD PTR [rdi+2568]
	mov rbp, QWORD PTR [rdi+2576]
	mov esi, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+3304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+3880], rax
23:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 24f
	mov rcx, r8
	and rcx, 127
	cmp rcx, 64
	jb 26f
	sub rcx, 128
	jmp 27f
26:
27:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	sbb r15, rdx
	sbb rbp, rdx
	sbb rsi, rdx
	mov BYTE PTR [rdi+rbx*1+3304], cl
	shr r8, 7
	mov rax, r9
	shl rax, 57
	or r8, rax
	shr r9, 7
	mov rax, r10
	shl rax, 57
	or r9, rax
	shr r10, 7
	mov rax, r11
	shl rax, 57
	or r10, rax
	shr r11, 7
	mov rax, r12
	shl rax, 57
	or r11, rax
	shr r12, 7
	mov rax, r13
	shl rax, 57
	or r12, rax
	shr r13, 7
	mov rax, r14
	shl rax, 57
	or r13, rax
	shr r14, 7
	mov rax, r15
	shl rax, 57
	or r14, rax
	shr r15, 7
	mov rax, rbp
	shl rax, 57
	or r15, rax
	shr rbp, 7
	mov rax, rsi
	shl rax, 57
	or rbp, rax
	shr rsi, 7
	add rbx, 7
	jmp 25f
24:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	mov rax, r15
	shl rax, 63
	or r14, rax
	shr r15, 1
	mov rax, rbp
	shl rax, 63
	or r15, rax
	shr rbp, 1
	mov rax, rsi
	shl rax, 63
	or rbp, rax
	shr rsi, 1
	add rbx, 1
25:
	cmp rbx, 577
	jb 23b
	mov r8, QWORD PTR [rdi+2584]
	mov r9, QWORD PTR [rdi+2592]
	mov r10, QWORD PTR [rdi+2600]
	mov r11, QWORD PTR [rdi+2608]
	mov r12, QWORD PTR [rdi+2616]
	mov r13, QWORD PTR [rdi+2624]
	mov r14, QWORD PTR [rdi+2632]
	mov r15, QWORD PTR [rdi+2640]
	mov rbp, QWORD PTR [rdi+2648]
	mov esi, 0
	mov ebx, 0
	movabs rax, 0
	mov QWORD PTR [rdi+5320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5352], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5496], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5504], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5512], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5576], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5584], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5592], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5600], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5608], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5616], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5624], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5632], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5640], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5712], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5720], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5728], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5736], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5744], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5752], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5760], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5768], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5776], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5784], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5792], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5800], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5808], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5816], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5824], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5832], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5840], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5848], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5856], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5864], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5872], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5880], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5888], rax
	movabs rax, 0
	mov QWORD PTR [rdi+5896], rax
28:
	mov rcx, r8
	and rcx, 1
	test rcx, rcx
	je 29f
	mov rcx, r8
	and rcx, 31
	cmp rcx, 16
	jb 211f
	sub rcx, 32
	jmp 212f
211:
212:
	mov rax, rcx
	shr rax, 63
	mov edx, 0
	sub rdx, rax
	sub r8, rcx
	sbb r9, rdx
	sbb r10, rdx
	sbb r11, rdx
	sbb r12, rdx
	sbb r13, rdx
	sbb r14, rdx
	sbb r15, rdx
	sbb rbp, rdx
	sbb rsi, rdx
	mov BYTE PTR [rdi+rbx*1+5320], cl
	shr r8, 5
	mov rax, r9
	shl rax, 59
	or r8, rax
	shr r9, 5
	mov rax, r10
	shl rax, 59
	or r9, rax
	shr r10, 5
	mov rax, r11
	shl rax, 59
	or r10, rax
	shr r11, 5
	mov rax, r12
	shl rax, 59
	or r11, rax
	shr r12, 5
	mov rax, r13
	shl rax, 59
	or r12, rax
	shr r13, 5
	mov rax, r14
	shl rax, 59
	or r13, rax
	shr r14, 5
	mov rax, r15
	shl rax, 59
	or r14, rax
	shr r15, 5
	mov rax, rbp
	shl rax, 59
	or r15, rax
	shr rbp, 5
	mov rax, rsi
	shl rax, 59
	or rbp, rax
	shr rsi, 5
	add rbx, 5
	jmp 210f
29:
	shr r8, 1
	mov rax, r9
	shl rax, 63
	or r8, rax
	shr r9, 1
	mov rax, r10
	shl rax, 63
	or r9, rax
	shr r10, 1
	mov rax, r11
	shl rax, 63
	or r10, rax
	shr r11, 1
	mov rax, r12
	shl rax, 63
	or r11, rax
	shr r12, 1
	mov rax, r13
	shl rax, 63
	or r12, rax
	shr r13, 1
	mov rax, r14
	shl rax, 63
	or r13, rax
	shr r14, 1
	mov rax, r15
	shl rax, 63
	or r14, rax
	shr r15, 1
	mov rax, rbp
	shl rax, 63
	or r15, rax
	shr rbp, 1
	mov rax, rsi
	shl rax, 63
	or rbp, rax
	shr rsi, 1
	add rbx, 1
210:
	cmp rbx, 577
	jb 28b
	mov r12, rsi
	mov esi, 1720
	mov edx, 424
	mov ecx, 424
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 3160
	mov ecx, 3160
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 2800
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -1080
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2800
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -1080
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 6120
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 7840
	mov rdx, QWORD PTR [rdi-5904]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3816], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-5896]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3808], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-5888]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3800], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-5880]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3792], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-5872]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3784], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-5864]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3776], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-5856]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3768], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-5848]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3760], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-5840]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3752], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3816
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2088
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 5904
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 7840
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -5904
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	add rdi, 424
	mov rdx, QWORD PTR [rdi+2736]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+3600], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi+2744]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+3608], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi+2752]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+3616], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi+2760]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+3624], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi+2768]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+3632], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi+2776]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+3640], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi+2784]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+3648], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi+2792]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+3656], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi+2800]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+3664], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 3600
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 3960
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7984
	add rdi, 7984
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7984
	add rdi, 1936
	xor eax, eax
	mov QWORD PTR [rdi+2088], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi+2096], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi+2104], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi+2112], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi+2120], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi+2128], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi+2136], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi+2144], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi+2152], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+2088]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+2088], rdx
	mov rdx, QWORD PTR [rdi+2096]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+2096], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+2104]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+2104], rdx
	mov rdx, QWORD PTR [rdi+2112]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+2112], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+2120]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+2120], rdx
	mov rdx, QWORD PTR [rdi+2128]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+2128], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+2136]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+2136], rdx
	mov rdx, QWORD PTR [rdi+2144]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi+2144], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi+2152]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi+2152], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, 2088
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 3816
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 7840
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -5976
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 5976
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 7840
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -5976
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 5976
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7840
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 5976
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7912
	add rdi, 7912
	mov rdx, QWORD PTR [rdi-5976]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3888], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-5968]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3880], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-5960]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3872], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-5952]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3864], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-5944]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3856], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-5936]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3848], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-5928]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3840], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-5920]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3832], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-5912]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3824], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3888
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 3888
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7912
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 7912
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -6120
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 6120
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 7912
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+6112], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+6120], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+6128], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+6136], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+6144], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+6152], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+6160], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+6168], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+6176], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+6184], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+6192], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+6200], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+6208], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+6216], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+6224], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+6232], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+6240], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+6248], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+6256], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+6264], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+6272], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+6280], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+6288], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+6296], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+6304], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+6312], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+6320], rax
	mov rax, QWORD PTR [rdi+2800]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+2808]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+2816]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+2824]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+2832]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+2840]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+2848]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+2856]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+2864]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+3160]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+3168]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+3176]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+3184]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+3192]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+3200]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+3208]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+3216]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+3224]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+424]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+432]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+440]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+448]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+456]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+464]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+472]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+480]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+488]
	mov QWORD PTR [rdi+1280], rax
	mov ebx, 1
213:
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	test rdx, rdx
	je 214f
	mov rdx, QWORD PTR [rdi+7984]
	or rdx, QWORD PTR [rdi+7992]
	or rdx, QWORD PTR [rdi+8000]
	or rdx, QWORD PTR [rdi+8008]
	or rdx, QWORD PTR [rdi+8016]
	or rdx, QWORD PTR [rdi+8024]
	or rdx, QWORD PTR [rdi+8032]
	or rdx, QWORD PTR [rdi+8040]
	or rdx, QWORD PTR [rdi+8048]
	test rdx, rdx
	je 216f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 7984
	xor eax, eax
	mov QWORD PTR [rdi-3960], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-3952], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-3944], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-3936], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-3928], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-3920], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-3912], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-3904], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-3896], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3960]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3960], rdx
	mov rdx, QWORD PTR [rdi-3952]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3952], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3944]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3944], rdx
	mov rdx, QWORD PTR [rdi-3936]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3936], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3928]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3928], rdx
	mov rdx, QWORD PTR [rdi-3920]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3920], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3912]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3912], rdx
	mov rdx, QWORD PTR [rdi-3904]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3904], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3896]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3896], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -3960
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2232
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1720
	mov rdx, QWORD PTR [rdi+6120]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+2304], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi+6128]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+2312], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi+6136]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+2320], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi+6144]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+2328], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi+6152]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+2336], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi+6160]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+2344], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi+6168]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+2352], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi+6176]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+2360], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi+6184]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+2368], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 2304
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2088
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 7984
	mov rdx, QWORD PTR [rdi-6840]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3960], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-6832]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3952], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-6824]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3944], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-6816]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3936], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-6808]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3928], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-6800]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3920], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-6792]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3912], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-6784]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3904], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-6776]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3896], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3960
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2016
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1216
	mov rdx, QWORD PTR [rdi+6696]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+2808], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi+6704]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+2816], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi+6712]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+2824], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi+6720]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+2832], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi+6728]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+2840], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi+6736]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+2848], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi+6744]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+2856], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi+6752]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+2864], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi+6760]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+2872], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 2808
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1944
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	mov r12, rsi
	mov esi, 2080
	mov edx, 2080
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2080
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	mov rdx, QWORD PTR [rdi+1936]
	or rdx, QWORD PTR [rdi+1944]
	or rdx, QWORD PTR [rdi+1952]
	or rdx, QWORD PTR [rdi+1960]
	or rdx, QWORD PTR [rdi+1968]
	or rdx, QWORD PTR [rdi+1976]
	or rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	test rdx, rdx
	je 218f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1864
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1288
	mov edx, 2080
	mov ecx, 2080
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	add rdi, 7984
	mov rdx, QWORD PTR [rdi-6768]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3960], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-6760]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3952], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-6752]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3944], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-6744]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3936], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-6736]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3928], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-6728]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3920], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-6720]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3912], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-6712]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3904], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-6704]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3896], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3960
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2592
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1432
	mov edx, 1432
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	jmp 219f
218:
	mov rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	or rdx, QWORD PTR [rdi+2112]
	or rdx, QWORD PTR [rdi+2120]
	or rdx, QWORD PTR [rdi+2128]
	or rdx, QWORD PTR [rdi+2136]
	or rdx, QWORD PTR [rdi+2144]
	test rdx, rdx
	je 220f
	movabs rax, 0
	mov QWORD PTR [rdi+1288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1496], rax
	jmp 221f
220:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
221:
219:
	jmp 217f
216:
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1216]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1224]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1232]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1240]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1248]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1256]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1264]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1272]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+1496], rax
217:
	jmp 215f
214:
	mov rax, QWORD PTR [rdi+7840]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+7848]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+7856]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+7864]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+7872]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+7880]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+7888]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+7896]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+7904]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+7912]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+7920]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+7928]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+7936]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+7944]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+7952]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+7960]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+7968]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+7976]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+7984]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+7992]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+8000]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+8008]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+8016]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+8024]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+8032]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+8040]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+8048]
	mov QWORD PTR [rdi+1496], rax
215:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	mov rax, rbx
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdi+1072]
	movdqu XMMWORD PTR [rdx], xmm0
	movdqu xmm1, XMMWORD PTR [rdi+1088]
	movdqu XMMWORD PTR [rdx+16], xmm1
	movdqu xmm2, XMMWORD PTR [rdi+1104]
	movdqu XMMWORD PTR [rdx+32], xmm2
	movdqu xmm3, XMMWORD PTR [rdi+1120]
	movdqu XMMWORD PTR [rdx+48], xmm3
	movdqu xmm4, XMMWORD PTR [rdi+1136]
	movdqu XMMWORD PTR [rdx+64], xmm4
	movdqu xmm5, XMMWORD PTR [rdi+1152]
	movdqu XMMWORD PTR [rdx+80], xmm5
	movdqu xmm6, XMMWORD PTR [rdi+1168]
	movdqu XMMWORD PTR [rdx+96], xmm6
	movdqu xmm7, XMMWORD PTR [rdi+1184]
	movdqu XMMWORD PTR [rdx+112], xmm7
	movdqu xmm8, XMMWORD PTR [rdi+1200]
	movdqu XMMWORD PTR [rdx+128], xmm8
	movdqu xmm9, XMMWORD PTR [rdi+1216]
	movdqu XMMWORD PTR [rdx+144], xmm9
	movdqu xmm10, XMMWORD PTR [rdi+1232]
	movdqu XMMWORD PTR [rdx+160], xmm10
	movdqu xmm11, XMMWORD PTR [rdi+1248]
	movdqu XMMWORD PTR [rdx+176], xmm11
	movdqu xmm12, XMMWORD PTR [rdi+1264]
	movdqu XMMWORD PTR [rdx+192], xmm12
	movdqu xmm13, XMMWORD PTR [rdi+1272]
	movdqu XMMWORD PTR [rdx+200], xmm13
	add rbx, 1
	cmp rbx, 8
	jb 213b
	add rdi, 6256
	xor eax, eax
	mov QWORD PTR [rdi-2232], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-2224], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-2216], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-2208], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-2200], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-2192], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-2184], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-2176], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-2168], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2232]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2232], rdx
	mov rdx, QWORD PTR [rdi-2224]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2224], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2216]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2216], rdx
	mov rdx, QWORD PTR [rdi-2208]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2208], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2200]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2200], rdx
	mov rdx, QWORD PTR [rdi-2192]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2192], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2184]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2184], rdx
	mov rdx, QWORD PTR [rdi-2176]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2176], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2168]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2168], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -2232
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4096
	add rdi, 6256
	mov rdx, QWORD PTR [rdi-2160]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-2232], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2152]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-2224], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2144]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-2216], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2136]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-2208], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2128]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-2200], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2120]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-2192], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2112]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-2184], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2104]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-2176], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2096]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-2168], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2232
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 144
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4168
	add rdi, 6472
	xor eax, eax
	mov QWORD PTR [rdi-2448], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-2440], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-2432], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-2424], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-2416], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-2408], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-2400], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-2392], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-2384], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2448]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2448], rdx
	mov rdx, QWORD PTR [rdi-2440]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2440], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2432]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2432], rdx
	mov rdx, QWORD PTR [rdi-2424]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2424], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2416]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2416], rdx
	mov rdx, QWORD PTR [rdi-2408]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2408], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2400]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2400], rdx
	mov rdx, QWORD PTR [rdi-2392]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2392], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2384]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2384], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -2448
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4240
	add rdi, 6472
	mov rdx, QWORD PTR [rdi-2232]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-2448], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2224]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-2440], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2216]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-2432], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2208]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-2424], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2200]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-2416], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2192]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-2408], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2184]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-2400], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2176]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-2392], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2168]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-2384], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2448
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 288
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4312
	add rdi, 6688
	xor eax, eax
	mov QWORD PTR [rdi-2664], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-2656], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-2648], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-2640], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-2632], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-2624], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-2616], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-2608], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-2600], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2664]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2664], rdx
	mov rdx, QWORD PTR [rdi-2656]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2656], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2648]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2648], rdx
	mov rdx, QWORD PTR [rdi-2640]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2640], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2632]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2632], rdx
	mov rdx, QWORD PTR [rdi-2624]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2624], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2616]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2616], rdx
	mov rdx, QWORD PTR [rdi-2608]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2608], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2600]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2600], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -2664
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4384
	add rdi, 6688
	mov rdx, QWORD PTR [rdi-2304]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-2664], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2296]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-2656], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2288]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-2648], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2280]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-2640], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2272]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-2632], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2264]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-2624], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2256]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-2616], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2248]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-2608], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2240]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-2600], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2664
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4456
	add rdi, 6904
	xor eax, eax
	mov QWORD PTR [rdi-2880], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-2872], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-2864], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-2856], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-2848], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-2840], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-2832], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-2824], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-2816], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2880]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2880], rdx
	mov rdx, QWORD PTR [rdi-2872]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2872], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2864]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2864], rdx
	mov rdx, QWORD PTR [rdi-2856]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2856], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2848]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2848], rdx
	mov rdx, QWORD PTR [rdi-2840]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2840], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2832]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2832], rdx
	mov rdx, QWORD PTR [rdi-2824]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-2824], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-2816]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-2816], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -2880
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4528
	add rdi, 6904
	mov rdx, QWORD PTR [rdi-2376]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-2880], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2368]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-2872], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2360]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-2864], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2352]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-2856], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2344]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-2848], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2336]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-2840], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2328]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-2832], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2320]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-2824], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2312]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-2816], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2880
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4600
	add rdi, 7120
	xor eax, eax
	mov QWORD PTR [rdi-3096], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-3088], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-3080], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-3072], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-3064], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-3056], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-3048], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-3040], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-3032], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3096]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3096], rdx
	mov rdx, QWORD PTR [rdi-3088]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3088], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3080]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3080], rdx
	mov rdx, QWORD PTR [rdi-3072]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3072], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3064]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3064], rdx
	mov rdx, QWORD PTR [rdi-3056]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3056], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3048]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3048], rdx
	mov rdx, QWORD PTR [rdi-3040]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3040], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3032]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3032], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -3096
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4672
	add rdi, 7120
	mov rdx, QWORD PTR [rdi-2448]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3096], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2440]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3088], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2432]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3080], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2424]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3072], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2416]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3064], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2408]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3056], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2400]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3048], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2392]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3040], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2384]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3032], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3096
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 720
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4744
	add rdi, 7336
	xor eax, eax
	mov QWORD PTR [rdi-3312], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-3304], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-3296], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-3288], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-3280], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-3272], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-3264], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-3256], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-3248], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3312]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3312], rdx
	mov rdx, QWORD PTR [rdi-3304]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3304], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3296]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3296], rdx
	mov rdx, QWORD PTR [rdi-3288]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3288], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3280]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3280], rdx
	mov rdx, QWORD PTR [rdi-3272]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3272], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3264]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3264], rdx
	mov rdx, QWORD PTR [rdi-3256]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3256], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3248]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3248], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -3312
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 792
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4816
	add rdi, 7336
	mov rdx, QWORD PTR [rdi-2520]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3312], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2512]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3304], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2504]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3296], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2496]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3288], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2488]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3280], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2480]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3272], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2472]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3264], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2464]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3256], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2456]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3248], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3312
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 864
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4888
	add rdi, 7552
	xor eax, eax
	mov QWORD PTR [rdi-3528], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-3520], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-3512], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-3504], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-3496], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-3488], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-3480], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-3472], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-3464], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3528]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3528], rdx
	mov rdx, QWORD PTR [rdi-3520]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3520], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3512]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3512], rdx
	mov rdx, QWORD PTR [rdi-3504]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3504], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3496]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3496], rdx
	mov rdx, QWORD PTR [rdi-3488]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3488], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3480]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3480], rdx
	mov rdx, QWORD PTR [rdi-3472]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3472], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3464]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3464], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -3528
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 936
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 4960
	add rdi, 7552
	mov rdx, QWORD PTR [rdi-2592]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3528], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2584]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3520], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2576]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3512], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2568]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3504], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2560]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3496], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2552]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3488], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2544]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3480], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2536]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3472], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2528]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3464], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3528
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1008
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 5032
	add rdi, 7768
	xor eax, eax
	mov QWORD PTR [rdi-3744], rax
	mov rdx, QWORD PTR [rdi]
	mulx r9, r8, QWORD PTR [rdi+8]
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov QWORD PTR [rdi-3736], r8
	mov r8d, 0
	mov rdx, QWORD PTR [rdi+8]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov QWORD PTR [rdi-3728], r9
	mov r9d, 0
	mov rdx, QWORD PTR [rdi+16]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov QWORD PTR [rdi-3720], r10
	mov r10d, 0
	mov rdx, QWORD PTR [rdi+24]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov QWORD PTR [rdi-3712], r11
	mov r11d, 0
	mov rdx, QWORD PTR [rdi+32]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov QWORD PTR [rdi-3704], r12
	mov r12d, 0
	mov rdx, QWORD PTR [rdi+40]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov QWORD PTR [rdi-3696], r13
	mov r13d, 0
	mov rdx, QWORD PTR [rdi+48]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov QWORD PTR [rdi-3688], r14
	mov r14d, 0
	mov rdx, QWORD PTR [rdi+56]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov QWORD PTR [rdi-3680], r15
	mov r15d, 0
	xor eax, eax
	mov rdx, QWORD PTR [rdi]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3744]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3744], rdx
	mov rdx, QWORD PTR [rdi-3736]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3736], rdx
	mov rdx, QWORD PTR [rdi+8]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3728]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3728], rdx
	mov rdx, QWORD PTR [rdi-3720]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3720], rdx
	mov rdx, QWORD PTR [rdi+16]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3712]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3712], rdx
	mov rdx, QWORD PTR [rdi-3704]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3704], rdx
	mov rdx, QWORD PTR [rdi+24]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3696]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3696], rdx
	mov rdx, QWORD PTR [rdi-3688]
	adcx rdx, rdx
	adox rdx, rcx
	mov QWORD PTR [rdi-3688], rdx
	mov rdx, QWORD PTR [rdi+32]
	mulx rcx, rax, rdx
	mov rdx, QWORD PTR [rdi-3680]
	adcx rdx, rdx
	adox rdx, rax
	mov QWORD PTR [rdi-3680], rdx
	adcx rbp, rbp
	adox rbp, rcx
	mov rdx, QWORD PTR [rdi+40]
	mulx rcx, rax, rdx
	adcx r8, r8
	adox r8, rax
	adcx r9, r9
	adox r9, rcx
	mov rdx, QWORD PTR [rdi+48]
	mulx rcx, rax, rdx
	adcx r10, r10
	adox r10, rax
	adcx r11, r11
	adox r11, rcx
	mov rdx, QWORD PTR [rdi+56]
	mulx rcx, rax, rdx
	adcx r12, r12
	adox r12, rax
	adcx r13, r13
	adox r13, rcx
	mov rdx, QWORD PTR [rdi+64]
	mulx rcx, rax, rdx
	adcx r14, r14
	adox r14, rax
	adcx r15, r15
	adox r15, rcx
	add rdi, -3744
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1080
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 5104
	add rdi, 7768
	mov rdx, QWORD PTR [rdi-2664]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-3744], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-2656]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-3736], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-2648]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-3728], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-2640]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-3720], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-2632]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-3712], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-2624]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-3704], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-2616]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-3696], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-2608]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-3688], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-2600]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-3680], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -3744
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1152
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 5176
	movabs rax, 0
	mov QWORD PTR [rdi+1072], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1080], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1088], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1096], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1104], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1112], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1120], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1128], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1136], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1144], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1152], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1160], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1200], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1208], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1216], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1224], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1232], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1240], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1248], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1256], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1264], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1272], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1280], rax
	mov ebx, 577
222:
	sub rbx, 1
	cmp rbx, 576
	je 223f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	jmp 224f
223:
224:
	movzx r8d, BYTE PTR [rdi+rbx*1+5320]
	test r8, r8
	je 225f
	cmp r8, 128
	jb 227f
	mov eax, 256
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu xmm9, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu xmm10, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu xmm11, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu xmm12, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu xmm13, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rax, r8
	sub rax, 1
	mov ecx, 72
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+5968], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+5984], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6000], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6016], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6032], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6048], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+6064], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+6080], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+6096], xmm8
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1576
	jmp 228f
227:
	mov rax, r8
	sub rax, 1
	shr rax, 1
	mov ecx, 216
	mul rcx
	mov rdx, rdi
	add rdx, 6112
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movdqu xmm9, XMMWORD PTR [rdx+144]
	movdqu XMMWORD PTR [rdi+1648], xmm9
	movdqu xmm10, XMMWORD PTR [rdx+160]
	movdqu XMMWORD PTR [rdi+1664], xmm10
	movdqu xmm11, XMMWORD PTR [rdx+176]
	movdqu XMMWORD PTR [rdi+1680], xmm11
	movdqu xmm12, XMMWORD PTR [rdx+192]
	movdqu XMMWORD PTR [rdi+1696], xmm12
	movdqu xmm13, XMMWORD PTR [rdx+200]
	movdqu XMMWORD PTR [rdi+1704], xmm13
	mov rax, r8
	sub rax, 1
	mov ecx, 72
	mul rcx
	mov rdx, rdi
	add rdx, 4096
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+5968], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+5984], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+6000], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+6016], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+6032], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+6048], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+6064], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+6080], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+6096], xmm8
228:
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	test rdx, rdx
	je 229f
	mov rdx, QWORD PTR [rdi+1648]
	or rdx, QWORD PTR [rdi+1656]
	or rdx, QWORD PTR [rdi+1664]
	or rdx, QWORD PTR [rdi+1672]
	or rdx, QWORD PTR [rdi+1680]
	or rdx, QWORD PTR [rdi+1688]
	or rdx, QWORD PTR [rdi+1696]
	or rdx, QWORD PTR [rdi+1704]
	or rdx, QWORD PTR [rdi+1712]
	test rdx, rdx
	je 231f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 5968
	mov rdx, QWORD PTR [rdi-4896]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-1944], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-4888]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-1936], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-4880]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-1928], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-4872]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-1920], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-4864]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-1912], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-4856]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-1904], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-4848]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-1896], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-4840]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-1888], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-4832]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-1880], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1944
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2160
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1936
	mov edx, 1504
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 6040
	mov rdx, QWORD PTR [rdi-4896]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi-2016], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-4888]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi-2008], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-4880]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi-2000], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-4872]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi-1992], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-4864]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi-1984], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-4856]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi-1976], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-4848]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi-1968], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-4840]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi-1960], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-4832]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi-1952], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2016
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -2016
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2008
	mov r12, rsi
	mov esi, 2080
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 2080
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2080
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	mov rdx, QWORD PTR [rdi+1936]
	or rdx, QWORD PTR [rdi+1944]
	or rdx, QWORD PTR [rdi+1952]
	or rdx, QWORD PTR [rdi+1960]
	or rdx, QWORD PTR [rdi+1968]
	or rdx, QWORD PTR [rdi+1976]
	or rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	test rdx, rdx
	je 233f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1864
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1288
	mov edx, 2080
	mov ecx, 2080
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 1216
	mov ecx, 1648
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1432
	mov edx, 1432
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	jmp 234f
233:
	mov rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	or rdx, QWORD PTR [rdi+2112]
	or rdx, QWORD PTR [rdi+2120]
	or rdx, QWORD PTR [rdi+2128]
	or rdx, QWORD PTR [rdi+2136]
	or rdx, QWORD PTR [rdi+2144]
	test rdx, rdx
	je 235f
	movabs rax, 0
	mov QWORD PTR [rdi+1288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1496], rax
	jmp 236f
235:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
236:
234:
	jmp 232f
231:
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1216]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1224]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1232]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1240]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1248]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1256]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1264]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1272]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1280]
	mov QWORD PTR [rdi+1496], rax
232:
	jmp 230f
229:
	mov rax, QWORD PTR [rdi+1504]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1512]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1520]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1528]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1648]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1656]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1496], rax
230:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	jmp 226f
225:
226:
	movzx r8d, BYTE PTR [rdi+rbx*1+3304]
	test r8, r8
	je 237f
	cmp r8, 128
	jb 239f
	mov eax, 256
	sub rax, r8
	mov r8, rax
	mov rax, r8
	sub rax, 1
	mov ecx, 144
	mul rcx
	lea rdx, {VG_P521_COMB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1712], rax
	add rdi, 280
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1296
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1576
	jmp 240f
239:
	mov rax, r8
	sub rax, 1
	mov ecx, 144
	mul rcx
	lea rdx, {VG_P521_COMB}
	add rdx, rax
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqu XMMWORD PTR [rdi+1504], xmm0
	movdqu xmm1, XMMWORD PTR [rdx+16]
	movdqu XMMWORD PTR [rdi+1520], xmm1
	movdqu xmm2, XMMWORD PTR [rdx+32]
	movdqu XMMWORD PTR [rdi+1536], xmm2
	movdqu xmm3, XMMWORD PTR [rdx+48]
	movdqu XMMWORD PTR [rdi+1552], xmm3
	movdqu xmm4, XMMWORD PTR [rdx+64]
	movdqu XMMWORD PTR [rdi+1568], xmm4
	movdqu xmm5, XMMWORD PTR [rdx+80]
	movdqu XMMWORD PTR [rdi+1584], xmm5
	movdqu xmm6, XMMWORD PTR [rdx+96]
	movdqu XMMWORD PTR [rdi+1600], xmm6
	movdqu xmm7, XMMWORD PTR [rdx+112]
	movdqu XMMWORD PTR [rdi+1616], xmm7
	movdqu xmm8, XMMWORD PTR [rdx+128]
	movdqu XMMWORD PTR [rdi+1632], xmm8
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1648], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1656], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1664], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1672], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1680], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1688], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1696], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1704], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1712], rax
240:
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	test rdx, rdx
	je 241f
	mov rax, QWORD PTR [rdi+1072]
	mov QWORD PTR [rdi+1864], rax
	mov rax, QWORD PTR [rdi+1080]
	mov QWORD PTR [rdi+1872], rax
	mov rax, QWORD PTR [rdi+1088]
	mov QWORD PTR [rdi+1880], rax
	mov rax, QWORD PTR [rdi+1096]
	mov QWORD PTR [rdi+1888], rax
	mov rax, QWORD PTR [rdi+1104]
	mov QWORD PTR [rdi+1896], rax
	mov rax, QWORD PTR [rdi+1112]
	mov QWORD PTR [rdi+1904], rax
	mov rax, QWORD PTR [rdi+1120]
	mov QWORD PTR [rdi+1912], rax
	mov rax, QWORD PTR [rdi+1128]
	mov QWORD PTR [rdi+1920], rax
	mov rax, QWORD PTR [rdi+1136]
	mov QWORD PTR [rdi+1928], rax
	mov rax, QWORD PTR [rdi+1144]
	mov QWORD PTR [rdi+2008], rax
	mov rax, QWORD PTR [rdi+1152]
	mov QWORD PTR [rdi+2016], rax
	mov rax, QWORD PTR [rdi+1160]
	mov QWORD PTR [rdi+2024], rax
	mov rax, QWORD PTR [rdi+1168]
	mov QWORD PTR [rdi+2032], rax
	mov rax, QWORD PTR [rdi+1176]
	mov QWORD PTR [rdi+2040], rax
	mov rax, QWORD PTR [rdi+1184]
	mov QWORD PTR [rdi+2048], rax
	mov rax, QWORD PTR [rdi+1192]
	mov QWORD PTR [rdi+2056], rax
	mov rax, QWORD PTR [rdi+1200]
	mov QWORD PTR [rdi+2064], rax
	mov rax, QWORD PTR [rdi+1208]
	mov QWORD PTR [rdi+2072], rax
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1936
	mov edx, 1504
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 1576
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2080
	mov edx, 2080
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 2080
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -72
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2080
	mov rdx, QWORD PTR [rdi+1936]
	or rdx, QWORD PTR [rdi+1944]
	or rdx, QWORD PTR [rdi+1952]
	or rdx, QWORD PTR [rdi+1960]
	or rdx, QWORD PTR [rdi+1968]
	or rdx, QWORD PTR [rdi+1976]
	or rdx, QWORD PTR [rdi+1984]
	or rdx, QWORD PTR [rdi+1992]
	or rdx, QWORD PTR [rdi+2000]
	test rdx, rdx
	je 243f
	mov r12, rsi
	mov esi, 1720
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1720
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1864
	mov edx, 1864
	mov ecx, 1720
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1288
	mov edx, 2080
	mov ecx, 2080
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 504
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -504
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 2080
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 2008
	mov edx, 2008
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -648
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1432
	mov edx, 1216
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	jmp 244f
243:
	mov rdx, QWORD PTR [rdi+2080]
	or rdx, QWORD PTR [rdi+2088]
	or rdx, QWORD PTR [rdi+2096]
	or rdx, QWORD PTR [rdi+2104]
	or rdx, QWORD PTR [rdi+2112]
	or rdx, QWORD PTR [rdi+2120]
	or rdx, QWORD PTR [rdi+2128]
	or rdx, QWORD PTR [rdi+2136]
	or rdx, QWORD PTR [rdi+2144]
	test rdx, rdx
	je 245f
	movabs rax, 0
	mov QWORD PTR [rdi+1288], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1296], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1304], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1312], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1320], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1328], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1336], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1344], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1352], rax
	movabs rax, 36028797018963968
	mov QWORD PTR [rdi+1360], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1368], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1376], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1384], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1392], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1400], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1408], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1416], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1424], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1432], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1440], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1448], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1456], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1464], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1472], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1480], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1488], rax
	movabs rax, 0
	mov QWORD PTR [rdi+1496], rax
	jmp 246f
245:
	mov r12, rsi
	mov esi, 1720
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1144
	mov ecx, 1144
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	mov r12, rsi
	mov esi, 1864
	mov edx, 1072
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	mov r12, rsi
	mov esi, 1936
	mov edx, 1936
	mov ecx, 1288
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1936
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, -648
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 648
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 0
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1936
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1864
	mov r12, rsi
	mov esi, 1432
	mov edx, 1144
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1432
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1432
	mov r12, rsi
	mov esi, 1288
	mov edx, 1936
	mov ecx, 1936
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1288
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -576
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1288
	add rdi, 1864
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -576
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 72
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
	mov r12, rsi
	mov esi, 1360
	mov edx, 1936
	mov ecx, 1360
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	mov r12, rsi
	mov esi, 1792
	mov edx, 1792
	mov ecx, 1792
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1792
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rbp, rbp
	adc r8, r8
	adc r9, r9
	adc r10, r10
	adc r11, r11
	adc r12, r12
	adc r13, r13
	adc r14, r14
	adc r15, r15
	mov rax, r15
	shr rax, 9
	add rbp, rax
	and r15, 511
	add rdi, 0
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1792
	add rdi, 1360
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 432
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, -432
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 1360
246:
244:
	jmp 242f
241:
	mov rax, QWORD PTR [rdi+1504]
	mov QWORD PTR [rdi+1288], rax
	mov rax, QWORD PTR [rdi+1512]
	mov QWORD PTR [rdi+1296], rax
	mov rax, QWORD PTR [rdi+1520]
	mov QWORD PTR [rdi+1304], rax
	mov rax, QWORD PTR [rdi+1528]
	mov QWORD PTR [rdi+1312], rax
	mov rax, QWORD PTR [rdi+1536]
	mov QWORD PTR [rdi+1320], rax
	mov rax, QWORD PTR [rdi+1544]
	mov QWORD PTR [rdi+1328], rax
	mov rax, QWORD PTR [rdi+1552]
	mov QWORD PTR [rdi+1336], rax
	mov rax, QWORD PTR [rdi+1560]
	mov QWORD PTR [rdi+1344], rax
	mov rax, QWORD PTR [rdi+1568]
	mov QWORD PTR [rdi+1352], rax
	mov rax, QWORD PTR [rdi+1576]
	mov QWORD PTR [rdi+1360], rax
	mov rax, QWORD PTR [rdi+1584]
	mov QWORD PTR [rdi+1368], rax
	mov rax, QWORD PTR [rdi+1592]
	mov QWORD PTR [rdi+1376], rax
	mov rax, QWORD PTR [rdi+1600]
	mov QWORD PTR [rdi+1384], rax
	mov rax, QWORD PTR [rdi+1608]
	mov QWORD PTR [rdi+1392], rax
	mov rax, QWORD PTR [rdi+1616]
	mov QWORD PTR [rdi+1400], rax
	mov rax, QWORD PTR [rdi+1624]
	mov QWORD PTR [rdi+1408], rax
	mov rax, QWORD PTR [rdi+1632]
	mov QWORD PTR [rdi+1416], rax
	mov rax, QWORD PTR [rdi+1640]
	mov QWORD PTR [rdi+1424], rax
	mov rax, QWORD PTR [rdi+1648]
	mov QWORD PTR [rdi+1432], rax
	mov rax, QWORD PTR [rdi+1656]
	mov QWORD PTR [rdi+1440], rax
	mov rax, QWORD PTR [rdi+1664]
	mov QWORD PTR [rdi+1448], rax
	mov rax, QWORD PTR [rdi+1672]
	mov QWORD PTR [rdi+1456], rax
	mov rax, QWORD PTR [rdi+1680]
	mov QWORD PTR [rdi+1464], rax
	mov rax, QWORD PTR [rdi+1688]
	mov QWORD PTR [rdi+1472], rax
	mov rax, QWORD PTR [rdi+1696]
	mov QWORD PTR [rdi+1480], rax
	mov rax, QWORD PTR [rdi+1704]
	mov QWORD PTR [rdi+1488], rax
	mov rax, QWORD PTR [rdi+1712]
	mov QWORD PTR [rdi+1496], rax
242:
	mov rax, QWORD PTR [rdi+1288]
	mov QWORD PTR [rdi+1072], rax
	mov rax, QWORD PTR [rdi+1296]
	mov QWORD PTR [rdi+1080], rax
	mov rax, QWORD PTR [rdi+1304]
	mov QWORD PTR [rdi+1088], rax
	mov rax, QWORD PTR [rdi+1312]
	mov QWORD PTR [rdi+1096], rax
	mov rax, QWORD PTR [rdi+1320]
	mov QWORD PTR [rdi+1104], rax
	mov rax, QWORD PTR [rdi+1328]
	mov QWORD PTR [rdi+1112], rax
	mov rax, QWORD PTR [rdi+1336]
	mov QWORD PTR [rdi+1120], rax
	mov rax, QWORD PTR [rdi+1344]
	mov QWORD PTR [rdi+1128], rax
	mov rax, QWORD PTR [rdi+1352]
	mov QWORD PTR [rdi+1136], rax
	mov rax, QWORD PTR [rdi+1360]
	mov QWORD PTR [rdi+1144], rax
	mov rax, QWORD PTR [rdi+1368]
	mov QWORD PTR [rdi+1152], rax
	mov rax, QWORD PTR [rdi+1376]
	mov QWORD PTR [rdi+1160], rax
	mov rax, QWORD PTR [rdi+1384]
	mov QWORD PTR [rdi+1168], rax
	mov rax, QWORD PTR [rdi+1392]
	mov QWORD PTR [rdi+1176], rax
	mov rax, QWORD PTR [rdi+1400]
	mov QWORD PTR [rdi+1184], rax
	mov rax, QWORD PTR [rdi+1408]
	mov QWORD PTR [rdi+1192], rax
	mov rax, QWORD PTR [rdi+1416]
	mov QWORD PTR [rdi+1200], rax
	mov rax, QWORD PTR [rdi+1424]
	mov QWORD PTR [rdi+1208], rax
	mov rax, QWORD PTR [rdi+1432]
	mov QWORD PTR [rdi+1216], rax
	mov rax, QWORD PTR [rdi+1440]
	mov QWORD PTR [rdi+1224], rax
	mov rax, QWORD PTR [rdi+1448]
	mov QWORD PTR [rdi+1232], rax
	mov rax, QWORD PTR [rdi+1456]
	mov QWORD PTR [rdi+1240], rax
	mov rax, QWORD PTR [rdi+1464]
	mov QWORD PTR [rdi+1248], rax
	mov rax, QWORD PTR [rdi+1472]
	mov QWORD PTR [rdi+1256], rax
	mov rax, QWORD PTR [rdi+1480]
	mov QWORD PTR [rdi+1264], rax
	mov rax, QWORD PTR [rdi+1488]
	mov QWORD PTR [rdi+1272], rax
	mov rax, QWORD PTR [rdi+1496]
	mov QWORD PTR [rdi+1280], rax
	jmp 238f
237:
238:
	test rbx, rbx
	jne 222b
	mov r12, rsi
	mov esi, 1216
	mov edx, 1216
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	movabs rax, 0
	mov QWORD PTR [rdi+2512], rax
	movabs rax, 70368744177664
	mov QWORD PTR [rdi+2520], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2528], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2536], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2544], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2552], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2560], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2568], rax
	movabs rax, 0
	mov QWORD PTR [rdi+2576], rax
	movabs rax, 360287970189639679
	mov QWORD PTR [rdi+2152], rax
	movabs rax, -2927982029091333070
	mov QWORD PTR [rdi+2160], rax
	movabs rax, -1720978806102766045
	mov QWORD PTR [rdi+2168], rax
	movabs rax, 3873067094995862738
	mov QWORD PTR [rdi+2176], rax
	movabs rax, -204699087262476341
	mov QWORD PTR [rdi+2184], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2192], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2200], rax
	movabs rax, -1
	mov QWORD PTR [rdi+2208], rax
	movabs rax, 511
	mov QWORD PTR [rdi+2216], rax
	movabs rax, 4940528924288850934
	mov QWORD PTR [rdi+136], rax
	movabs rax, -4302566813442262959
	mov QWORD PTR [rdi+144], rax
	movabs rax, -9208736750959699409
	mov QWORD PTR [rdi+152], rax
	movabs rax, -5874531763869423212
	mov QWORD PTR [rdi+160], rax
	movabs rax, 5
	mov QWORD PTR [rdi+168], rax
	movabs rax, 0
	mov QWORD PTR [rdi+176], rax
	movabs rax, 0
	mov QWORD PTR [rdi+184], rax
	movabs rax, 0
	mov QWORD PTR [rdi+192], rax
	movabs rax, 0
	mov QWORD PTR [rdi+200], rax
	add rdi, 2512
	mov rdx, QWORD PTR [rdi-216]
	xor eax, eax
	mulx r8, rax, QWORD PTR [rdi]
	mov QWORD PTR [rdi+1512], rax
	mulx r9, rax, QWORD PTR [rdi+8]
	adcx r8, rax
	mulx r10, rax, QWORD PTR [rdi+16]
	adcx r9, rax
	mulx r11, rax, QWORD PTR [rdi+24]
	adcx r10, rax
	mulx r12, rax, QWORD PTR [rdi+32]
	adcx r11, rax
	mulx r13, rax, QWORD PTR [rdi+40]
	adcx r12, rax
	mulx r14, rax, QWORD PTR [rdi+48]
	adcx r13, rax
	mulx r15, rax, QWORD PTR [rdi+56]
	adcx r14, rax
	mulx rbp, rax, QWORD PTR [rdi+64]
	adcx r15, rax
	adc rbp, 0
	mov rdx, QWORD PTR [rdi-208]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r8, rax
	adcx r9, rcx
	mov QWORD PTR [rdi+1520], r8
	mov r8d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox rbp, rax
	adcx r8, rcx
	mov eax, 0
	adox r8, rax
	mov rdx, QWORD PTR [rdi-200]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r9, rax
	adcx r10, rcx
	mov QWORD PTR [rdi+1528], r9
	mov r9d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r8, rax
	adcx r9, rcx
	mov eax, 0
	adox r9, rax
	mov rdx, QWORD PTR [rdi-192]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r10, rax
	adcx r11, rcx
	mov QWORD PTR [rdi+1536], r10
	mov r10d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r9, rax
	adcx r10, rcx
	mov eax, 0
	adox r10, rax
	mov rdx, QWORD PTR [rdi-184]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r11, rax
	adcx r12, rcx
	mov QWORD PTR [rdi+1544], r11
	mov r11d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r10, rax
	adcx r11, rcx
	mov eax, 0
	adox r11, rax
	mov rdx, QWORD PTR [rdi-176]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r12, rax
	adcx r13, rcx
	mov QWORD PTR [rdi+1552], r12
	mov r12d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r11, rax
	adcx r12, rcx
	mov eax, 0
	adox r12, rax
	mov rdx, QWORD PTR [rdi-168]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r13, rax
	adcx r14, rcx
	mov QWORD PTR [rdi+1560], r13
	mov r13d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r14, rax
	adcx r15, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r12, rax
	adcx r13, rcx
	mov eax, 0
	adox r13, rax
	mov rdx, QWORD PTR [rdi-160]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r14, rax
	adcx r15, rcx
	mov QWORD PTR [rdi+1568], r14
	mov r14d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox r15, rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r13, rax
	adcx r14, rcx
	mov eax, 0
	adox r14, rax
	mov rdx, QWORD PTR [rdi-152]
	xor eax, eax
	mulx rcx, rax, QWORD PTR [rdi]
	adox r15, rax
	adcx rbp, rcx
	mov QWORD PTR [rdi+1576], r15
	mov r15d, 0
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, 1512
	mov edx, 512
	xor eax, eax
	cmp rax, -1
	mulx rcx, rax, QWORD PTR [rdi]
	adox rax, QWORD PTR [rdi+64]
	mov QWORD PTR [rdi+64], rax
	adcx rbp, rcx
	mulx rcx, rax, QWORD PTR [rdi+8]
	adox rbp, rax
	adcx r8, rcx
	mulx rcx, rax, QWORD PTR [rdi+16]
	adox r8, rax
	adcx r9, rcx
	mulx rcx, rax, QWORD PTR [rdi+24]
	adox r9, rax
	adcx r10, rcx
	mulx rcx, rax, QWORD PTR [rdi+32]
	adox r10, rax
	adcx r11, rcx
	mulx rcx, rax, QWORD PTR [rdi+40]
	adox r11, rax
	adcx r12, rcx
	mulx rcx, rax, QWORD PTR [rdi+48]
	adox r12, rax
	adcx r13, rcx
	mulx rcx, rax, QWORD PTR [rdi+56]
	adox r13, rax
	adcx r14, rcx
	mulx rcx, rax, QWORD PTR [rdi+64]
	adox r14, rax
	adcx r15, rcx
	mov eax, 0
	adox r15, rax
	add rdi, -1512
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2512
	mov r12, rsi
	mov esi, 2584
	mov edx, 2512
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1512
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2944
	add rdi, 2512
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, -360
	xor eax, eax
	cmp rax, -1
	adc rbp, QWORD PTR [rdi]
	adc r8, QWORD PTR [rdi+8]
	adc r9, QWORD PTR [rdi+16]
	adc r10, QWORD PTR [rdi+24]
	adc r11, QWORD PTR [rdi+32]
	adc r12, QWORD PTR [rdi+40]
	adc r13, QWORD PTR [rdi+48]
	adc r14, QWORD PTR [rdi+56]
	adc r15, QWORD PTR [rdi+64]
	add rdi, 360
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2512
	mov r12, rsi
	mov esi, 2584
	mov edx, 2512
	mov ecx, 1216
	call {vg_p521_mul_mod_p_adx}
	mov rsi, r12
	add rdi, 1072
	mov rbp, QWORD PTR [rdi]
	mov r8, QWORD PTR [rdi+8]
	mov r9, QWORD PTR [rdi+16]
	mov r10, QWORD PTR [rdi+24]
	mov r11, QWORD PTR [rdi+32]
	mov r12, QWORD PTR [rdi+40]
	mov r13, QWORD PTR [rdi+48]
	mov r14, QWORD PTR [rdi+56]
	mov r15, QWORD PTR [rdi+64]
	add rdi, 1512
	sub rbp, QWORD PTR [rdi]
	sbb r8, QWORD PTR [rdi+8]
	sbb r9, QWORD PTR [rdi+16]
	sbb r10, QWORD PTR [rdi+24]
	sbb r11, QWORD PTR [rdi+32]
	sbb r12, QWORD PTR [rdi+40]
	sbb r13, QWORD PTR [rdi+48]
	sbb r14, QWORD PTR [rdi+56]
	sbb r15, QWORD PTR [rdi+64]
	add r15, 512
	add rdi, 216
	mov rax, r15
	shr rax, 9
	xor rax, 1
	sub rbp, rax
	sbb r8, 0
	sbb r9, 0
	sbb r10, 0
	sbb r11, 0
	sbb r12, 0
	sbb r13, 0
	sbb r14, 0
	sbb r15, 0
	and r15, 511
	mov QWORD PTR [rdi], rbp
	mov QWORD PTR [rdi+8], r8
	mov QWORD PTR [rdi+16], r9
	mov QWORD PTR [rdi+24], r10
	mov QWORD PTR [rdi+32], r11
	mov QWORD PTR [rdi+40], r12
	mov QWORD PTR [rdi+48], r13
	mov QWORD PTR [rdi+56], r14
	mov QWORD PTR [rdi+64], r15
	sub rdi, 2800
	mov rdx, QWORD PTR [rdi+2944]
	or rdx, QWORD PTR [rdi+2952]
	or rdx, QWORD PTR [rdi+2960]
	or rdx, QWORD PTR [rdi+2968]
	or rdx, QWORD PTR [rdi+2976]
	or rdx, QWORD PTR [rdi+2984]
	or rdx, QWORD PTR [rdi+2992]
	or rdx, QWORD PTR [rdi+3000]
	or rdx, QWORD PTR [rdi+3008]
	cmp rdx, 1
	sbb rdx, rdx
	mov rbp, rdx
	mov rdx, QWORD PTR [rdi+2296]
	sub rdx, QWORD PTR [rdi+136]
	mov rdx, QWORD PTR [rdi+2304]
	sbb rdx, QWORD PTR [rdi+144]
	mov rdx, QWORD PTR [rdi+2312]
	sbb rdx, QWORD PTR [rdi+152]
	mov rdx, QWORD PTR [rdi+2320]
	sbb rdx, QWORD PTR [rdi+160]
	mov rdx, QWORD PTR [rdi+2328]
	sbb rdx, QWORD PTR [rdi+168]
	mov rdx, QWORD PTR [rdi+2336]
	sbb rdx, QWORD PTR [rdi+176]
	mov rdx, QWORD PTR [rdi+2344]
	sbb rdx, QWORD PTR [rdi+184]
	mov rdx, QWORD PTR [rdi+2352]
	sbb rdx, QWORD PTR [rdi+192]
	mov rdx, QWORD PTR [rdi+2360]
	sbb rdx, QWORD PTR [rdi+200]
	sbb rax, rax
	mov r12, rax
	mov rdx, QWORD PTR [rdi+2800]
	or rdx, QWORD PTR [rdi+2808]
	or rdx, QWORD PTR [rdi+2816]
	or rdx, QWORD PTR [rdi+2824]
	or rdx, QWORD PTR [rdi+2832]
	or rdx, QWORD PTR [rdi+2840]
	or rdx, QWORD PTR [rdi+2848]
	or rdx, QWORD PTR [rdi+2856]
	or rdx, QWORD PTR [rdi+2864]
	cmp rdx, 1
	sbb rdx, rdx
	and rdx, r12
	or rdx, rbp
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rdx, QWORD PTR [rdi+1216]
	or rdx, QWORD PTR [rdi+1224]
	or rdx, QWORD PTR [rdi+1232]
	or rdx, QWORD PTR [rdi+1240]
	or rdx, QWORD PTR [rdi+1248]
	or rdx, QWORD PTR [rdi+1256]
	or rdx, QWORD PTR [rdi+1264]
	or rdx, QWORD PTR [rdi+1272]
	or rdx, QWORD PTR [rdi+1280]
	mov ecx, 0
	sub rcx, rdx
	sbb rdx, rdx
	mov rax, QWORD PTR [rdi+3232]
	and rax, rdx
	mov QWORD PTR [rdi+3232], rax
	mov rax, QWORD PTR [rdi+3232]
	and rax, 1
	mov rbx, QWORD PTR [rdi]
	mov rbp, QWORD PTR [rdi+8]
	mov r12, QWORD PTR [rdi+16]
	mov r13, QWORD PTR [rdi+24]
	mov r14, QWORD PTR [rdi+32]
	mov r15, QWORD PTR [rdi+40]
	ret
	.p2align 6
