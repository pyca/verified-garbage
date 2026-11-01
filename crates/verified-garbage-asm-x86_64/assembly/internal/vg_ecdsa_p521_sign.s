// The functions of `src/internal/vg_ecdsa_p521_sign.rs` of `verified-garbage-asm-x86_64`, as text: generated from
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
